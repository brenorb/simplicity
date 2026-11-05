{-# LANGUAGE ScopedTypeVariables,RankNTypes #-}
-- | Complete bounded BIP157/158 client query. Authenticated checkpoint/request
-- are program parameters; the one raw filter witness is consumed by dataflow.
module JetDiscovery.Lib.CompactFilters
 (Context(..),Proof,filterKernel,filterProof,entry) where
import Prelude hiding(drop,take,not,and,or)
import qualified Prelude as P
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import Data.Bits(shiftL)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic(eq)
import qualified Simplicity.Programs.Arith as A
import qualified Simplicity.Programs.Word as W
import Simplicity.Programs.Sha256.Lib
import Simplicity.Ty.Word
import JetDiscovery.Lib.Bytes
import qualified JetDiscovery.Lib.SipHash as Sip
import qualified JetDiscovery.Ref.CompactFilters as R
import qualified JetDiscovery.Ref.Bip340 as EC
import JetDiscovery.Types
import JetDiscovery.Tx(unhex,mkEnv,mkTx,mkInput,mkOutput,dummyOutpoint,defaultTap)

-- Word512 contains the complete raw filter, left aligned; every unused bit
-- must be zero. Length is bytes. Native encoding/hash/GCS parsing are checked.
type Proof=(Word8,Word512)
data Context=Context{rawBlockHash::B.ByteString,previousHeaderRaw::B.ByteString
 ,expectedHeaderRaw::B.ByteString,watchScript::B.ByteString,expectedMatch::Bool}
-- remaining N, F, target, raw stream, available bits, previous value, match
type State=(Word8,(Word32,(Word32,(Word512,(Word16,(Word32,Bit))))))
type Unary=(State,(Word32,Bit))
nleft :: Core t => t State Word8
nleft=oh
range,target,previous :: Core t => t State Word32
range=ioh;target=iioh;previous=ih>>>ih>>>ih>>>ih>>>ih>>>oh
stream :: Core t => t State Word512
stream=ih>>>ih>>>ih>>>oh
available :: Core t => t State Word16
available=ih>>>ih>>>ih>>>ih>>>oh
found :: Core t => t State Bit
found=ih>>>ih>>>ih>>>ih>>>ih>>>ih
mkState :: (Core t,TyC x) => t x Word8 -> t x Word32 -> t x Word32 -> t x Word512 -> t x Word16 -> t x Word32 -> t x Bit -> t x State
mkState n f t s b p m=n&&&(f&&&(t&&&(s&&&(b&&&(p&&&m)))))
same :: (Assert t,TyC x,TyC y) => t x y -> t x y -> t x()
same a b=(a&&&b)>>>eq>>>verify
shiftStream :: Core t => Integer -> t Word512 Word512
shiftStream n=(konst(w16 n)&&&iden)>>>W.left_shift word16 word512
minus16 :: Assert t => Integer -> t Word16 Word16
minus16 n=(iden&&&konst(w16 n))>>>A.subtract word16>>>ih
minus8 :: Assert t => Integer -> t Word8 Word8
minus8 n=(iden&&&konst(w8 n))>>>A.subtract word8>>>ih
extend16 :: Core t => t Word16 Word512
extend16=konst(toWord256 0)&&&(konst(toWord128 0)&&&(konst(w64 0)&&&(konst(w32 0)&&&(konst(w16 0)&&&iden))))
bitLength :: Assert t => t Proof Word16
bitLength=((konst(w8 0)&&&oh)&&&konst(w16 8))>>>A.multiply word16>>>ih
sha32 :: Assert t => t Word256 Word256
sha32=((unit>>>ctx8Init)&&&iden)>>>ctx8Add32>>>ctx8Finalize
shortHash :: forall t. Assert t => t Proof Word256
shortHash=((unit>>>iv)&&&padded)>>>hashBlock
 where
  pad :: t Proof Word512
  pad=(bitLength&&&konst(toWord512(1`shiftL`511)))>>>W.right_shift word16 word512
  padded :: t Proof Word512
  padded=(((ih&&&pad)>>>W.bitwise_or word512)&&&(bitLength>>>extend16))>>>W.bitwise_or word512
filterHeader :: Assert t => B.ByteString -> t Proof Word256
filterHeader previousRaw=((unit>>>ctx8Init)&&&((shortHash>>>sha32)&&&konst(w256FromBytes previousRaw)))>>>ctx8Add64>>>ctx8Finalize>>>sha32
firstByte :: Core t => t Word512 Word8
firstByte=oh>>>oh>>>oh>>>oh>>>oh>>>oh
initial :: forall t. Assert t => Context -> t Proof State
initial context=mkState count f query(ih>>>shiftStream 8)(bitLength>>>minus16 8)(konst(w32 0))false
 where
  count :: t Proof Word8
  count=ih>>>firstByte
  f :: t Proof Word32
  f=((konst(w16 0)&&&(konst(w8 0)&&&count))&&&konst(w32 784931))>>>A.multiply word32>>>ih
  sip :: t Proof Word64
  sip=(konst(w64 key0,w64 key1)&&&konst(buffer511FromBytes(watchScript context)))>>>Sip.sipHash24
  query :: t Proof Word32
  query=(sip&&&(konst(w32 0)&&&f))>>>A.multiply word64>>>oh>>>ih
  little bytes=P.sum[toInteger b`shiftL`(8*i)|(i,b)<-zip[0..](B.unpack bytes)]
  key0=little(B.take 8(rawBlockHash context));key1=little(B.take 8(B.drop 8(rawBlockHash context)))
unaryStep :: forall t. Assert t => t Unary Unary
unaryStep=(iih&&&iden)>>>cond iden active
 where
  bit :: t Unary Bit
  bit=oh>>>stream>>>oh>>>oh>>>oh>>>oh>>>oh>>>oh>>>oh>>>oh>>>oh
  consume :: t State State
  consume=mkState nleft range target(stream>>>shiftStream 1)(available>>>minus16 1)previous found
  updatedQ :: t Unary Word32
  updatedQ=(bit&&&iden)>>>cond((ioh&&&konst(w32 1))>>>A.add word32>>>ih)ioh
  active :: t Unary Unary
  active=((((konst(w16 1)&&&(oh>>>available))>>>A.le word16>>>verify)&&&iden)>>>ih)
   >>>((oh>>>consume)&&&(updatedQ&&&(not bit)))
decodeOne :: forall t. Assert t => t State State
decodeOne=(iden&&&(konst(w32 0)&&&false))>>>P.foldr(>>>)iden(P.replicate 24 unaryStep)>>>finish
 where
  remainder :: t Unary Word32
  remainder=((konst(w8 13)&&&(oh>>>stream>>>oh>>>oh>>>oh>>>oh))>>>W.right_shift word8 word32)
  delta :: t Unary Word32
  delta=((((konst(w8 19)&&&ioh)>>>W.left_shift word8 word32)&&&remainder)>>>W.bitwise_or word32)
  addValue :: t Unary(Bit,Word32)
  addValue=((oh>>>previous)&&&delta)>>>A.add word32
  value :: t Unary Word32
  value=(((addValue>>>oh>>>not iden>>>verify)&&&(addValue>>>ih))>>>ih)
  finish :: t Unary State
  finish=(((iih>>>verify)&&&((konst(w16 19)&&&(oh>>>available))>>>A.le word16>>>verify)
    &&&((value&&&(oh>>>range))>>>A.lt word32>>>verify))&&&iden)>>>ih
   >>>mkState(oh>>>nleft>>>minus8 1)(oh>>>range)(oh>>>target)(oh>>>stream>>>shiftStream 19)
     (oh>>>available>>>minus16 19)value(((oh>>>found)&&&((value&&&(oh>>>target))>>>eq))>>>or oh ih)
step :: Assert t => t State State
step=(((nleft&&&konst(w8 0))>>>eq)&&&iden)>>>cond iden decodeOne
filterKernel :: forall t. Assert t => Context -> t Proof()
filterKernel context
 |B.length(rawBlockHash context)/=32||B.length(previousHeaderRaw context)/=32||B.length(expectedHeaderRaw context)/=32||B.length(watchScript context)>511=error "bounded compact-filter context"
 |otherwise=(((shape&&&authenticated)&&&initial context)>>>ih)>>>P.foldr(>>>)iden(P.replicate 16 step)>>>final
 where
  shape :: t Proof()
  shape=(((konst(w8 1)&&&oh)>>>A.le word8>>>verify)
    &&&((oh&&&konst(w8 44))>>>A.le word8>>>verify)
    &&&((ih>>>firstByte&&&konst(w8 16))>>>A.le word8>>>verify))>>>unit
  authenticated :: t Proof()
  authenticated=same(filterHeader(previousHeaderRaw context))(konst(w256FromBytes(expectedHeaderRaw context)))
  final :: t State()
  final=(same nleft(konst(w8 0))&&&same stream(konst(toWord512 0))
    &&&((available&&&konst(w16 8))>>>A.lt word16>>>verify)
    &&&same found(if expectedMatch context then true else false))>>>unit
filterProof raw
 |B.length raw>44=error "filter exceeds44-byte bound"
 |otherwise=(w8(toInteger(B.length raw)),toWord512(EC.intFromBytes(raw<>B.replicate(64-B.length raw)0)))
fields delimiter s=case break(==delimiter)s of(a,[])->[a];(a,_:b)->a:fields delimiter b
entry :: IO Entry
entry=do
 rows<-map(fields '\t').P.drop 1.lines <$>readFile "vendor-specs/bitcoin-growth4/bip158-all-vectors.tsv"
 let [_,_,display,_,previousRaw,encoded,expectedRaw,items,_,_]=rows!!5
     script=unhex(P.head(fields ',' items));raw=unhex encoded
     context=Context(R.displayHashToRaw display)(R.displayHashToRaw previousRaw)(R.displayHashToRaw expectedRaw)script True
     proof=filterProof raw
     -- Pure client predicate: the harness's default Bitcoin environment is
     -- irrelevant, but the trusted checkpoint/request are committed constants.
     vector name witness expected=Vector name defaultEnv witness expected
     defaultEnv=mkEnv(mkTx 2[mkInput(dummyOutpoint 0)100000(BL.fromStrict(unhex "51"))0xffffffff][mkOutput 99000(unhex "51")]0)0 defaultTap
 return(Entry "app-bip157-158-filter-query" "BIP157/158 authenticated compact-filter query with actual GCS parse, header chain and SipHash range mapping"
  "BIP157/158 pinned a0c977f3755da6476b955677ca9318334a2432c4; CC0-1.0; all10official testnet block vectors"
  BitcoinApp(Derived "One complete bounded client predicate, canonical basic filters N<=16/raw<=44bytes; registered fixture is official testnet height180480")
  ["CLIENT MODE: trusted filter-header and blockhash checkpoints plus watched output script are committed client parameters; filter headers are not Bitcoin consensus commitments",
   "Peer checkpoint agreement and full-block recomputation on disagreement, chain/finality authentication and the truth/completeness of source block filters remain external BIP157 client obligations",
   "Actual basic filter parameters P19/M784931; SipHash keys use first16RAWblockhash bytes interpreted as two little-endian64bit integers; explorer/display strings convert only at named external codec boundary",
   "Single raw filter witness; Simplicity hashes the exact canonical bytes, verifies filterHeader=SHA256d(SHA256d(filter)||previousHeader), parses every unary/remainder/delta and checks exact membership",
   "N0..16,raw1..44bytes,one watched script<=511bytes; one query family, not separate credit per block,count or positive/negative result; matching may be a BIP158 false positive requiring full block download",
   "Full official10-row source inventory/ref reconstruction retained; application fixture uses real published13-item block, not an invented block or shortened source window"]
  (boundProgram(filterKernel context))
  [vector "official13-item testnet filter and authenticated matching script" proof Accept,
   vector "raw filter data bit changed"(filterProof(B.take 1 raw<>B.singleton(B.index raw 1+1)<>B.drop 2 raw))Reject,
   vector "canonical filter from different actual block"(filterProof(unhex((rows!!4)!!5)))Reject,
   vector "declared raw length truncated"(w8(toInteger(B.length raw-1)),snd proof)Reject,
   vector "extra zero byte is not canonical padding"(w8(toInteger(B.length raw+1)),snd proof)Reject,
   vector "raw length zero"(w8 0,snd proof)Reject,
   vector "raw length45 exceeds proved single-block bound"(w8 45,snd proof)Reject,
   vector "nonzero data outside claimed raw byte length"(fst proof,toWord512(fromWord512(snd proof)+1))Reject])
