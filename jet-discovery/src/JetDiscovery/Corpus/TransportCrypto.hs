{-# LANGUAGE RankNTypes #-}
-- | Bitcoin P2P cryptographic building blocks, counted as components rather
-- than complete transport clients. All public inputs enter through one witness.
module JetDiscovery.Corpus.TransportCrypto (entries) where
import Prelude hiding (take,drop)
import qualified Prelude as P
import qualified Data.ByteString as B
import Data.Bits (shiftL,xor)
import Simplicity.Term.Core
import Simplicity.Programs.Generic (eq)
import Simplicity.Programs.Bit (verify)
import Simplicity.Ty.Word
import qualified Simplicity.Bitcoin.Term as T
import JetDiscovery.Types
import JetDiscovery.Tx
import JetDiscovery.Lib.Bytes
import qualified JetDiscovery.Lib.SipHash as S
import qualified JetDiscovery.Ref.SipHash as R
import qualified JetDiscovery.Lib.ChaCha20 as C
import qualified JetDiscovery.Ref.ChaCha20 as RC
import qualified JetDiscovery.Lib.Poly1305 as M
import qualified JetDiscovery.Ref.Poly1305 as RM

type Proof=(((Word64,Word64),Buffer511 Word8),Word64)
kernel :: T.Simplicity t => t Proof ()
kernel=(take S.sipHash24&&&ih)>>>eq>>>verify
little :: B.ByteString -> Integer
little bytes=P.sum [toInteger b `shiftL`(8*i)|(i,b)<-zip [0..](B.unpack bytes)]
split :: String -> [String]
split s=case break(=='\t')s of(a,[])->[a];(a,_:b)->a:split b
entries :: IO [Entry]
entries=concat <$> sequence[sipEntries,chachaEntries,polyEntries]
sipEntries :: IO [Entry]
sipEntries=do
 rows<-map split . P.drop 1 . lines <$> readFile "vendor-specs/transport-crypto/siphash24-vectors.tsv"
 if length rows/=64 then error "SipHash expected all64 official vectors" else pure()
 let official=[(read n,unhex key,unhex msg,unhex expected)|[n,key,msg,expected]<-rows]
 if length official/=64 || map (\(n,_,m,_)->(n,B.length m)) official/=[(n,n)|n<-[0..63]]
   then error "SipHash vector inventory malformed" else pure()
 let reference key msg=R.sipHash24(fromInteger(little(B.take 8 key)))(fromInteger(little(B.drop 8 key)))msg
 if not(and[reference key msg==fromInteger(little expected)|(_,key,msg,expected)<-official])
   then error "SipHash independent reference disagrees with official vectors" else pure()
 let proof key msg expected=(((w64(little(B.take 8 key)),w64(little(B.drop 8 key))),buffer511FromBytes msg),w64 expected)
     environment=mkEnv(mkTx 2[mkInput(dummyOutpoint 0)1000 mempty 0][mkOutput 900 mempty]0)0 defaultTap
     original=[Vector("official length"++show n)environment(proof key msg(little expected))Accept|(n,key,msg,expected)<-official]
     key=B.pack[0..15]
     message :: Int -> B.ByteString
     message n=B.pack[fromIntegral(t `mod`256)|t<-[0..n-1]]
     derived n=let msg=message n in Vector("derived length boundary"++show n)environment(proof key msg(toInteger(reference key msg)))Accept
     good=proof key(B.pack[0..31])(toInteger(reference key(B.pack[0..31])))
     (input,expected)=good
     ((k0,k1),buffer)=input
     negatives=[Vector "changed digest" environment(input,w64(fromWord64 expected `xor`1))Reject,
       Vector "changed key" environment(((w64(fromWord64 k0 `xor`1),k1),buffer),expected)Reject,
       Vector "changed actual message length" environment(proof key(B.pack[0..30])(fromWord64 expected))Reject]
 pure[Entry "crypto-siphash24" "Full bounded SipHash2-4 for Bitcoin compact blocks and Golomb-coded filters"
   "Aumasson/Bernstein SipHash2-4/64bit; pinned reference32d067603b93b47828700880649198e0bfbbcffa; BIP152/BIP158 use"
   BitcoinApp(Upstream "All64 official64bit vectors in vendor-specs/transport-crypto/siphash24-vectors.tsv; seven derived block/length boundaries and three adversarial vectors")
   ["COMPONENT: unsigned64bit SipHash2-4,128bit key interpreted as two little-endian words; message0..511bytes",
    "All message bytes, key and claimed digest are bound operands; no per-block witness hints; exact tail/low8bit-length finalization",
    "BIP152 compact-block shortIDs and BIP158 range reduction/filter decoding are separate client protocols, not implemented by this hash kernel",
    "No SipHash128/halfSipHash/round-count or message-length variant receives extra counting credit"]
   (boundProgram kernel)(original++map derived[64,65,127,128,255,256,511]++negatives)]

pack8 [a,b,c,d,e,f,g,h]=(((a,b),(c,d)),((e,f),(g,h)))
pack8 _=error "TransportCrypto.pack8"
pack16 xs=(pack8(P.take 8 xs),pack8(P.drop 8 xs))
wordsLE bytes=[w32(little(B.take 4(B.drop i bytes)))|i<-[0,4..B.length bytes-1]]
type ChaChaProof=(C.Parameters,Vector16 Word32)
chachaKernel :: T.Simplicity t => t ChaChaProof ()
chachaKernel=(take C.chacha20Block&&&ih)>>>eq>>>verify
chachaEntries :: IO [Entry]
chachaEntries=do
 rows<-map split . P.drop 1 . lines <$> readFile "vendor-specs/transport-crypto/chacha20-block-vectors.tsv"
 if length rows/=6 || any((/=5).length)rows then error "ChaCha20 all6 RFC completeblock cases required" else pure()
 let cases=[(name,unhex key,read counter::Integer,unhex nonce,unhex result)|[name,key,counter,nonce,result]<-rows]
 if not(and[B.length key==32&&B.length nonce==12&&B.length result==64&&
          RC.block key(fromInteger counter)nonce==result|(_,key,counter,nonce,result)<-cases])
   then error "ChaCha20 independent reference disagrees with primary KAT" else pure()
 let proof key counter nonce result=
       let [n0,n1,n2]=wordsLE nonce
       in ((pack8(wordsLE key),(w32 counter,(n0,(n1,n2)))),pack16(wordsLE result))
     environment=mkEnv(mkTx 2[mkInput(dummyOutpoint 0)1000 mempty 0][mkOutput 900 mempty]0)0 defaultTap
     official=[Vector("RFC8439 "++name)environment(proof key counter nonce result)Accept|(name,key,counter,nonce,result)<-cases]
     key=B.pack[255,254..224];nonce=B.pack[7..18]
     derived counter=Vector("derived counter boundary"++show counter)environment(proof key counter nonce(RC.block key(fromInteger counter)nonce))Accept
     (_,k0,c0,n0,r0)=head cases
     good@(parameters,expected)=proof k0 c0 n0 r0
     (keyWords,(counter,(nx,(ny,nz))))=parameters
     ((((e0,e1),e23),e47),rest)=expected
     negatives=[Vector "changed keystream word" environment(parameters,((((w32(fromWord32 e0 `xor`1),e1),e23),e47),rest))Reject,
       Vector "changed block counter" environment((keyWords,(w32(fromWord32 counter `xor`1),(nx,(ny,nz)))),expected)Reject,
       Vector "changed nonce word" environment((keyWords,(counter,(w32(fromWord32 nx `xor`1),(ny,nz)))),expected)Reject]
 pure[Entry "crypto-chacha20-block" "Complete RFC8439 ChaCha20 block function for Bitcoin encrypted transport"
   "RFC8439 sections2.3/2.3.2 and AppendixA.1; BIP324 FSChaCha20/FSChaCha20Poly1305 dependency"
   BitcoinApp(Upstream "All6 published RFC8439 completeblock KATs;3derived counterboundaries and3adversarial vectors")
   ["COMPONENT: fixed256bit key,96bit IETFnonce,32bit blockcounter and20rounds with exact feedforward; numerical words are little-endian decoded",
    "One complete64byte keystream block; counter increment/exhaustion, encryption XOR, Poly1305 composition, session handshake and rekeying belong to their client protocol",
    "Cipher modes, message lengths and counter/profile variants share one ChaCha20 family; no full BIP324 session credit",
    "Public witness-key benchmark is not a claim of onchain confidential encryption or authorization"]
   (boundProgram chachaKernel)(official++map derived[0,1,4294967295]++negatives)]

type PolyProof=((Word256,Buffer511 Word8),Word128)
polyKernel :: T.Simplicity t => t PolyProof ()
polyKernel=(take M.poly1305&&&ih)>>>eq>>>verify
polyEntries :: IO [Entry]
polyEntries=do
 rows<-map split . P.drop 1 . lines <$> readFile "vendor-specs/transport-crypto/poly1305-vectors.tsv"
 if length rows/=12 || any((/=4).length)rows then error "Poly1305 all12 RFC cases required" else pure()
 let cases=[(name,unhex key,unhex message,unhex tag)|[name,key,message,tag]<-rows]
 if not(and[B.length key==32&&B.length message<=511&&B.length tag==16&&RM.poly1305 key message==tag|(name,key,message,tag)<-cases])
   then error "Poly1305 independent Integer reference disagrees with primary KAT" else pure()
 let proof key message tag=((w256FromBytes key,buffer511FromBytes message),toWord128(little tag))
     environment=mkEnv(mkTx 2[mkInput(dummyOutpoint 0)1000 mempty 0][mkOutput 900 mempty]0)0 defaultTap
     official=[Vector("RFC8439 "++name)environment(proof key message tag)Accept|(name,key,message,tag)<-cases]
     (_,key,message,tag)=head cases
     derived n=let m=B.pack[fromIntegral(t `mod`256)|t<-[0..n-1::Int]] in Vector("derived block boundary"++show n)environment(proof key m(RM.poly1305 key m))Accept
     flipFirst bytes=B.cons(B.head bytes `xor`1)(B.tail bytes)
     negatives=[Vector "changed tag" environment(proof key message(flipFirst tag))Reject,
       Vector "changed unclamped key bit" environment(proof(flipFirst key)message tag)Reject,
       Vector "changed final message length" environment(proof key(B.init message)tag)Reject]
     clampKey=B.take 3 key<>B.singleton(B.index key 3 `xor`0xf0)<>B.drop 4 key
     clamp=Vector "clamped-away raw key bits retain the standard MAC" environment(proof clampKey message tag)Accept
 pure[Entry "crypto-poly1305" "Full bounded Poly1305 with exact130-bit reduction and partial-block handling"
   "RFC8439 section2.5/2.5.2 and AppendixA.3; BIP324 ChaCha20Poly1305 dependency"
   BitcoinApp(Upstream "All12 published RFC8439 Poly1305 MAC cases, including every reduction/carry edge;14derived length boundaries,clamp invariance and3adversarial cases")
   ["COMPONENT: raw256bit one-time key, message0..511bytes and complete128bit tag; exact standard clamping, block1-marker and little-endian codecs",
    "No supplied quotients/inverses/accumulators: multiplication and two exactpseudoMersenne folds compute the complete MAC; canonical accumulator mod2^130-5, final addition mod2^128",
    "One-time key generation/nonce discipline, confidentiality, AEAD framing and BIP324 handshake/rekey are protocol boundaries; a public witness key is not onchain authentication",
    "Block counts and MAC/framing variants share one Poly1305 family and never add parameter-sweep credit"]
   (boundProgram polyKernel)(official++map derived[0,1,7,8,15,16,17,31,32,127,128,255,256,511]++[clamp]++negatives)]
