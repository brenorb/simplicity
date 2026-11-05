{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}
-- | Contract verification paths with actual expensive arithmetic/hash work.
-- Bounds are fixed at compile time; no account ledger or foreign consensus is implied.
module JetDiscovery.Corpus.ContractExpansion
 ( entries, keccakFixed, ecdsaVerify, ecRecover ) where
import Prelude hiding (drop,take,not,and,or)
import qualified Prelude as P
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BC
import Data.Bits (testBit)
import qualified Data.List as L
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as A
import qualified Simplicity.Programs.Word as W
import qualified Simplicity.Programs.LibSecp256k1.Lib as S
import Simplicity.Ty.Word hiding (Vector)
import JetDiscovery.Corpus.Hashes (keccakF)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Bip340 as R
import qualified JetDiscovery.Ref.Keccak as K

type Aff = (Word256,Word256)
type Sig = (Word256,Word256)
type Rec = (Word256,(Word256,(Word256,Bit)))

pick :: (Core t,TyC a,TyC b) => Bool -> t a b -> t (a,a) b
pick False = take
pick True = drop
at32 :: (Core t,TyC a) => Int -> t (Vector32 a) a
at32 i = pick (testBit i 4) (pick (testBit i 3) (pick (testBit i 2) (pick (testBit i 1) (pick (testBit i 0) iden))))
mk8 :: (Core t,TyC a,TyC b) => [t a b] -> t a (Vector8 b)
mk8 [a,b,c,d,e,f,g,h] = ((a&&&b)&&&(c&&&d))&&&((e&&&f)&&&(g&&&h))
mk8 _ = error "mk8"
mk32 :: (Core t,TyC a,TyC b) => [t a b] -> t a (Vector32 b)
mk32 xs = (mk8 (P.take 8 xs)&&&mk8 (P.take 8 (P.drop 8 xs)))&&&(mk8 (P.take 8 (P.drop 16 xs))&&&mk8 (P.drop 24 xs))
bytes32 :: (Core t,TyC a) => t a Word256 -> [t a Word8]
bytes32 x = [x >>> at32 i | i<-[0..31]]

-- | Keccak-256 of a fixed byte string of expressions, including padding and all blocks.
keccakFixed :: forall t a. (Assert t,TyC a) => [t a Word8] -> t a Word256
keccakFixed bytes = (iden &&& konst (toWord word2048 0)) >>> blocks >>> drop result
 where
  n=136-P.length bytes `mod`136
  pad=if n==1 then [0x81] else 1:replicate (n-2) 0++[0x80]
  padded=bytes++map (konst . w8) pad
  chunks []=[]
  chunks xs=P.take 136 xs:chunks (P.drop 136 xs)
  block :: [t a Word8] -> t (a,Vector32 Word64) (a,Vector32 Word64)
  block bs=oh &&& (mk32 [lane i|i<-[0..31]] >>> keccakF)
   where
    lane i | i>=17 = drop (at32 i)
           | otherwise=(drop (at32 i)&&&take (mk8 (P.reverse (P.take 8 (P.drop (8*i) bs)))))>>>W.bitwise_xor word64
  blocks=L.foldl' (>>>) iden (map block (chunks padded))
  result=((at32 0>>>bswap64)&&&(at32 1>>>bswap64))&&&((at32 2>>>bswap64)&&&(at32 3>>>bswap64))

rangeScalar :: Assert t => t Word256 ()
rangeScalar = ((iden&&&konst (w256 0)>>>eq>>>not iden>>>verify)&&&(iden&&&konst (w256 R.n)>>>A.lt word256>>>verify))>>>unit

-- | Full ECDSA verifier using existing secp256k1 primitives, no inversion hint.
-- Input ((Q,z),(r,s)); rejects infinity, off-curve Q, and noncanonical/zero r,s.
ecdsaVerify :: Assert t => t ((Aff,Word256),Sig) ()
ecdsaVerify = (checks&&&iden)>>>drop (iden&&&(drop (drop S.scalar_invert)))>>>calc
 where
  checks=(((take (take oh)&&&konst (w256 R.p))>>>A.lt word256>>>verify)&&&((take (take ih)&&&konst (w256 R.p))>>>A.lt word256>>>verify)&&&(take (take S.ge_is_on_curve)>>>verify)&&&(drop (take rangeScalar)&&&drop (drop rangeScalar)))>>>unit
  -- Input to calc is (original operands, checked s inverse). Both products
  -- reuse this actual value rather than recomputing scalar_invert twice.
  u1=(take oih&&&ih)>>>S.scalar_multiply
  u2=(take ioh&&&ih)>>>S.scalar_multiply
  qj=take ooh&&&konst (w256 1)
  calc=(((u2&&&qj)&&&u1)>>>S.linear_combination_1>>>S.gej_normalize>>>verify>>>oh>>>S.scalar_normalize)&&&take ioh>>>eq>>>verify

-- | Ethereum ecrecover (v=27/28 represented as parity bit): Q=r^-1(sR-zG).
-- This includes decompression, canonical scalar checks, normalization and Keccak address.
ecRecover :: Assert t => t Rec Word256
ecRecover=(checks&&&iden)>>>drop (iden&&&(ioh>>>S.scalar_invert))>>>recover
 where
  -- The inverse is produced once before recovery and reused by a and b.
  r=take ioh
  s=take iioh
  z=take oh
  ri=ih
  rp=(take iiih&&&r)>>>S.decompress>>>verify
  rj=rp&&&konst (w256 1)
  a=(s&&&ri)>>>S.scalar_multiply
  b=((z>>>S.scalar_negate)&&&ri)>>>S.scalar_multiply
  checks=((ioh>>>rangeScalar)&&&(iioh>>>rangeScalar))>>>unit
  recover=(((a&&&rj)&&&b)>>>S.linear_combination_1>>>S.gej_normalize>>>verify>>>keccakFixed (bytes32 oh++bytes32 ih))>>>maskAddress
  maskAddress=(iden&&&konst (w256 (2^160-1)))>>>W.bitwise_and word256

-- | Exact ERC2612 typed-data digest; expiration needs an authenticated clock
-- when deployed on Bitcoin (the transaction nLockTime is only a lower bound).
type PermitFields = (Word256,(Word256,(Word256,Word256)))
permitDigest :: Assert t => Word256 -> Word256 -> t PermitFields Word256
permitDigest domain owner = structHash>>>keccakFixed ([konst (w8 0x19),konst (w8 1)]++bytes32 (konst domain)++bytes32 iden)
 where
  typ=w256FromBytes (K.keccak256 (BC.pack "Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)"))
  structHash=keccakFixed (bytes32 (konst typ)++bytes32 (konst owner)++bytes32 oh++bytes32 ioh++bytes32 iioh++bytes32 iiih)
permitAuth :: (Assert t,Witness t) => Word256 -> Word256 -> (PermitFields,(Word256,(Word256,Bit))) -> t () ()
permitAuth domain owner w=witness w>>>permitAuthT domain owner
permitAuthT :: Assert t => Word256 -> Word256 -> t (PermitFields,(Word256,(Word256,Bit))) ()
permitAuthT domain owner=(nonceOk&&&signatureOk)>>>unit
 where
  fields=oh
  nonceOk=(fields>>>iioh)&&&konst (w256 7)>>>eq>>>verify
  signatureOk=((fields>>>permitDigest domain owner)&&&ih>>>ecRecover)&&&konst owner>>>eq>>>verify

-- | All19 guardian slots are represented once. Absent slots add zero; present
-- slots verify their own guardian address, preventing duplicate-index counting.
-- The body is exactly64 bytes, including51 bytes of header and13 of payload.
wormholeQuorum :: (Assert t,Witness t) => Word512 -> [Maybe (Word256,(Word256,Bit))] -> t () ()
wormholeQuorum body signatures=konst (w8 13)&&&(witness body>>>bodyHash>>>count)>>>A.le word8>>>verify
 where
  bodyHash=keccakFixed (bytes32 oh++bytes32 ih)>>>keccakFixed (bytes32 iden)
  slot i=witness (maybe (Left ()) Right (signatures!!i))&&&iden>>>match (konst (w8 0))
    (((ih&&&oh)>>>ecRecover)&&&konst (w256 (addr (toInteger i+1)))>>>eq>>>verify>>>konst (w8 1))
  count=L.foldl' (\acc i->(acc&&&slot i)>>>A.add word8>>>ih) (konst (w8 0)) [0..18]

simpleEnv=mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap
h :: BS.ByteString -> Integer
h=R.intFromBytes . K.keccak256
addr :: Integer -> Integer
addr sk = case R.pointMul R.gPt sk of Just (x,y)->h (R.bytesFromInt x<>R.bytesFromInt y) `mod`2^160; _->error "addr"
inv :: Integer -> Integer -> Integer
inv x m=go x (m-2) 1 where go _ 0 a=a; go b e a=go (b*b`mod`m) (e`div`2) (if odd e then a*b`mod`m else a)
signEcdsa :: Integer -> Integer -> Integer -> (Integer,(Integer,Bool))
signEcdsa sk z k = case R.pointMul R.gPt k of Just (x,y)->(x`mod`R.n,(((z+(x`mod`R.n)*sk)*inv k R.n)`mod`R.n,odd y)); _->error "signEcdsa"
recW (z,(r,(s,v)))=(w256 z,(w256 r,(w256 s,if v then Right () else Left ())))

authEntry :: String -> String -> String -> Integer -> [Vector (Integer,(Integer,(Integer,Bool)))] -> Entry
authEntry ident title spec owner vs=Entry ident title spec CrossChain (Derived "Keccak reference checked against canonical empty/abc digests; ECDSA point arithmetic in Ref.Bip340")
 ["hash is a 32-byte witness operand; signature uses Ethereum v=27/28, no EIP-155 transaction encoding", "address is constant; this is signature authorization, not an account ledger"]
 (\w->Prog ((witness (recW w)>>>ecRecover)&&&konst (w256 owner)>>>eq>>>verify)) vs

entries :: [Entry]
entries = permitEntries ++ wormholeEntries ++
 [Entry "xchain-secp256k1-ecdsa" "Full secp256k1 ECDSA verification" "SEC1 v2 section 4.1.4; FIPS 186-5 ECDSA verification" CrossChain
  (Derived "signatures generated with independent Integer secp256k1 reference; boundary and malformed-key negatives")
  ["Q,z,r,s are witness operands; scalar inversion runs in the program", "canonical r,s in [1,n-1]; high-s is accepted (mathematical ECDSA)"]
  (\(q,z,(r,s))->Prog (witness (((w256 (fst q),w256 (snd q)),w256 z),(w256 r,w256 s))>>>ecdsaVerify))
  [Vector "valid ECDSA" simpleEnv (q,z,(r,s)) Accept, Vector "changed message" simpleEnv (q,z+1,(r,s)) Reject,
   Vector "zero r" simpleEnv (q,z,(0,s)) Reject,Vector "s equals n" simpleEnv (q,z,(r,R.n)) Reject,
   Vector "off-curve public key" simpleEnv ((fst q,snd q+1),z,(r,s)) Reject,
   Vector "canonical point x=1" simpleEnv ((1,q1y),0,(1,1)) Accept,
   Vector "noncanonical point x=p+1" simpleEnv ((R.p+1,q1y),0,(1,1)) Reject]
 ,authEntry "xchain-ecrecover" "Ethereum ecrecover address authorization" "Ethereum Yellow Paper ECREC precompile; SEC1 public-key recovery" (addr sk)
  [Vector "v=27/28 recovers owner" simpleEnv rec Accept,Vector "wrong recovery parity" simpleEnv (z,(r,(s,P.not v))) Reject,
   Vector "changed digest" simpleEnv (z+1,(r,(s,v))) Reject,Vector "zero s" simpleEnv (z,(r,(0,v))) Reject,
   Vector "noncanonical r" simpleEnv (z,(R.n,(s,v))) Reject]
 ,Entry "xchain-keccak-merkle-membership" "Keccak binary Merkle membership (compressed asset proof path)" "Metaplex Bubblegum / SPL account-compression binary Keccak Merkle authentication; four-level bounded tree" CrossChain
  (Derived "root computed by independent Keccak reference") ["leaf hash is supplied; metadata leaf construction and concurrent-tree changelog are outside this path", "fixed depth four; each sibling hash and ordering bit enter together once as witness data"]
  (\(leaf,path)->Prog ((witness (w256FromBytes leaf)>>>merkle path)&&&konst (w256FromBytes root)>>>eq>>>verify))
  [Vector "valid compressed asset membership" simpleEnv (leaf,path) Accept,
   Vector "wrong leaf" simpleEnv (BS.replicate 32 0,path) Reject,
   Vector "wrong sibling order" simpleEnv (leaf,(True,snd (head path)):tail path) Reject,
   Vector "changed sibling hash" simpleEnv (leaf,(fst (head path),BS.replicate 32 0):tail path) Reject]
 ]
 where
 sk=42
 z=h (BC.pack "jet-discovery ECDSA")
 Just q=R.pointMul R.gPt sk
 Just (_,q1y)=R.liftX 1
 (r,(s,v))=signEcdsa sk z 17
 rec=(z,(r,(s,v)))
 leaf=K.keccak256 (BC.pack "compressed asset leaf")
 path=[(odd i,BS.replicate 32 (fromIntegral i))|i<-[2..5]]
 root=L.foldl' (\a (d,b)->K.keccak256 (if d then b<>a else a<>b)) leaf path
 merkle ps=L.foldl' (>>>) iden
   [ (witness (if d then Right () else Left (),w256FromBytes b)&&&iden)
      >>>(ooh&&&(oih&&&ih))
      >>>cond (keccakFixed (bytes32 oh++bytes32 ih)) (keccakFixed (bytes32 ih++bytes32 oh))
   |(d,b)<-ps]


permitEntries :: [Entry]
permitEntries=[Entry "xchain-eip712-permit" "ERC2612 EIP712 permit signature and nonce authorization" "ERC2612 typed Permit digest and EIP712 domain separation; pinned sources in vendor-specs/contracts/"
 CrossChain (Derived "exact ABI words hashed by independent Ref.Keccak and signed with Integer ECDSA reference")
 ["nonce is bound to constant7, representing one committed UTXO state; owner/domain are constants", "expiration is signed but requires an authenticated time source; Bitcoin nLockTime cannot establish an upper bound on current time", "this verifies permit authorization, not an ERC20 allowance ledger"]
 (\(sp,val,nonce,deadline,(r,(s,v)))->Prog (permitAuth (w256 domain) (w256 owner) ((w256 sp,(w256 val,(w256 nonce,w256 deadline))),(w256 r,(w256 s,if v then Right () else Left ())))))
 [Vector "valid permit" simpleEnv good Accept,Vector "altered value" simpleEnv (sp,val+1,7,deadline,signature) Reject,
  Vector "wrong committed nonce, correctly re-signed" simpleEnv (sp,val,8,deadline,signEcdsa sk (digest 8) 23) Reject,
  Vector "altered domain-bound deadline" simpleEnv (sp,val,7,deadline+1,signature) Reject]]
 where
 sk=42;owner=addr sk;domain=h (BC.pack "fixed chain and contract domain");sp=addr 99;val=100000;deadline=2000000000
 typ=K.keccak256 (BC.pack "Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)")
 digest nonce=h (BS.pack [0x19,1]<>R.bytesFromInt domain<>K.keccak256 (typ<>BS.concat (map R.bytesFromInt [owner,sp,val,nonce,deadline])))
 signature=signEcdsa sk (digest 7) 23
 good=(sp,val,7,deadline,signature)

wormholeEntries :: [Entry]
wormholeEntries=[Entry "xchain-wormhole-13-of-19" "Wormhole double-Keccak13-of-19 guardian quorum" "Wormhole VAA guardian signature body hash https://docs.wormhole.com/protocol/infrastructure/vaas/"
 CrossChain (Derived "nineteen independent Integer ECDSA signers; body double Keccak from Ref.Keccak; adversarial quorum and duplicate-slot vectors")
 ["exact64-byte body:51-byte VAA body header plus13-byte payload", "fixed19-member guardian set; at least13 valid distinct slots; set rotation, expiration and replay state belong to the enclosing bridge covenant", "this is the full bounded guardian-quorum check, not foreign-chain finality verification"]
 (\(body,sigs)->Prog (wormholeQuorum (w256FromBytes (BS.take 32 body),w256FromBytes (BS.drop 32 body)) (map (fmap toSig) sigs)))
 [Vector "thirteen distinct guardians" simpleEnv (body,valid) Accept,
  Vector "twelve guardians" simpleEnv (body,P.take 12 valid++replicate 7 Nothing) Reject,
  Vector "duplicate guardian signature in wrong slot" simpleEnv (body,head valid:head valid:P.drop 2 valid) Reject,
  Vector "body tampered" simpleEnv (BS.singleton 1<>BS.tail body,valid) Reject]]
 where
 body=BS.replicate 64 0x42
 digest=h (K.keccak256 body)
 valid=[if i<=13 then Just (signEcdsa i digest (100+i)) else Nothing | i<-[1..19]]
 toSig (r,(s,v))=(w256 r,(w256 s,if v then Right () else Left ()))
