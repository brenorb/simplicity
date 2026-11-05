{-# LANGUAGE ScopedTypeVariables,RankNTypes #-}
-- | Complete bounded BIP152 client reconstruction on a trusted legacy header.
module JetDiscovery.Lib.CompactBlock(entry,Proof,Fill,blockKernel,proofW) where
import qualified Prelude as P
import Prelude hiding(drop,take,not,and,or)
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic(eq)
import qualified Simplicity.Programs.Arith as A
import qualified Simplicity.Programs.Word as W
import Simplicity.Programs.Sha256.Lib
import Simplicity.Ty.Word
import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.TaprootTx1(appendConst)
import qualified JetDiscovery.Lib.SipHash as Sip
import qualified JetDiscovery.Ref.CompactBlock as R
import JetDiscovery.Types
import JetDiscovery.Tx

type Fill=Either(Buffer511 Word8)(Word256,(Word8,(Word256,Buffer511 Word8)))
type Proof=(Word64,(Word64,(Word8,(Buffer255 Word8,Fill))))
type Keys=(Word64,Word64)
type Prepared=(Keys,(Word256,(Word64,(Word256,Fill))))
type Rebuilt=(Keys,(Word64,(Word256,Word256)))
same :: (Assert t,TyC x,TyC y) => t x y -> t x y -> t x()
same a b=(a&&&b)>>>eq>>>verify
sha32 :: Assert t => t Word256 Word256
sha32=((unit>>>ctx8Init)&&&iden)>>>ctx8Add32>>>ctx8Finalize
hash511 :: Assert t => t(Buffer511 Word8)Word256
hash511=sha256Buffer511>>>sha32
hash255 :: Assert t => t(Buffer255 Word8)Word256
hash255=((unit>>>ctx8Init)&&&iden)>>>ctx8AddBuffer buffer255>>>ctx8Finalize>>>sha32
asBuffer32 :: Core t => t Word256(Buffer511 Word8)
asBuffer32=injl unit&&&(injl unit&&&(injl unit&&&(injr iden&&&(injl unit&&&(injl unit&&&(injl unit&&&(injl unit&&&injl unit)))))))
selector :: Assert t => B.ByteString -> t Word64 Keys
selector header=((unit>>>ctx8Init>>>appendConst header)&&&iden)>>>ctxAddLE64>>>ctx8Finalize
 >>>((oh>>>oh>>>bswap64)&&&(oh>>>ih>>>bswap64))
prepare :: forall t. Assert t => B.ByteString -> t Proof Prepared
prepare header=(((shape&&&iden)>>>ih))>>>(keys&&&(blockHash&&&(ioh&&&(coinbase&&&rest))))
 where
  shape :: t Proof()
  shape=(same iioh(konst(w8 0))&&&((ioh&&&konst(w64(2^48)))>>>A.lt word64>>>verify))>>>unit
  keys :: t Proof Keys
  keys=oh>>>selector header
  blockHash :: t Proof Word256
  blockHash=konst(buffer511FromBytes header)>>>hash511
  coinbase :: t Proof Word256
  coinbase=ih>>>ih>>>ih>>>oh>>>hash255
  rest :: t Proof Fill
  rest=ih>>>ih>>>ih>>>ih
fillHash :: forall t. Assert t => t(Word256,Fill)Word256
fillHash=(ih&&&oh)>>>match(oh>>>hash511)requested
 where
  requested :: t((Word256,(Word8,(Word256,Buffer511 Word8))),Word256)Word256
  requested=(((same ooh ih&&&same oioh(konst(w8 1))&&&same(oh>>>iioh)ih)&&&iden)>>>ih)
   >>>oh>>>ih>>>ih>>>ih>>>hash511
rebuild :: Assert t => t Prepared Rebuilt
rebuild=oh&&&(iioh&&&((ih>>>ih>>>ih>>>oh)&&&((ioh&&&(ih>>>ih>>>ih>>>ih))>>>fillHash)))
finish :: forall t. Assert t => B.ByteString -> t Rebuilt()
finish header=(same shortId ioh&&&same merkle(konst(w256FromBytes(B.take 32(B.drop 36 header)))))
 >>>unit
 where
  pairHash :: t Rebuilt(Word256,Word256)
  pairHash=ih>>>ih
  shortId :: t Rebuilt Word64
  shortId=((oh&&&(pairHash>>>ih>>>asBuffer32))>>>Sip.sipHash24)
   >>>(iden&&&konst(w64 0xffffffffffff))>>>W.bitwise_and word64
  merkle :: t Rebuilt Word256
  merkle=(((pairHash>>>eq>>>not iden>>>verify)&&&pairHash)>>>ih)
   >>>((unit>>>ctx8Init)&&&iden)>>>ctx8Add64>>>ctx8Finalize>>>sha32
blockKernel :: Assert t => B.ByteString -> t Proof()
blockKernel header|B.length header/=80=error "BIP152 header80"
 |otherwise=prepare header>>>rebuild>>>finish header
proofW nonce sid index cb fill=(w64 nonce,(w64 sid,(w8 index,(buf255 cb,case fill of
 R.Mempool raw->Left(buffer511FromBytes raw)
 R.Requested h i response raw->Right(w256FromBytes h,(w8 i,(w256FromBytes response,buffer511FromBytes raw)))))))
 where buf255 raw|B.length raw>255=error "coinbase255 bound"
                  |otherwise=fst(bufferFill buffer255(map(w8.toInteger)(B.unpack raw)))
fields s=case break(=='\t')s of(a,[])->[a];(a,_:b)->a:fields b
entry :: IO Entry
entry=do
 rows<-map fields.P.drop 1.lines <$>readFile "vendor-specs/bitcoin-growth5/bip152-historical-fixture.tsv"
 let field name=case[v|[k,v]<-rows,k==name]of[v]->v;_->error name
     header=unhex(field "header_raw");cb=unhex(field "coinbase_raw");transaction=unhex(field "transaction_raw")
     blockHash=unhex(field "block_hash_raw");nonce=read(field "compact_nonce");sid=R.shortId header nonce transaction
     requested=R.Requested blockHash 1 blockHash transaction
     make n s i coinbase fill=proofW n s i coinbase fill
     good=make nonce sid 0 cb requested
     flipFirst raw=B.singleton(B.head raw+1)<>B.tail raw
     env=mkEnv(mkTx 2[mkInput(dummyOutpoint 0)1000 BL.empty 0xffffffff][mkOutput 999(unhex "51")]0)0 defaultTap
     vector name proof expected=Vector name env proof expected
 return(Entry "app-bip152-compact-block-reconstruction"
  "Complete bounded BIP152 client: actual compact-block shortID, mempool/requested fill and full raw-transaction Merkle reconstruction"
  "BIP152 PD; Bitcoin Core v30.0 d0f6d9953a15d7c7111d46dcb76ab2bb18e5dee3 blockencodings, MIT; actual mainnet block170"
  BitcoinApp(Derived "Complete actual two-transaction block170; derived standard cmpctblock/getblocktxn/blocktxn wires and all8 Core source-procedure inventory")
  ["CLIENT MODE: actual80byte block header is an authenticated client parameter; header chain/PoW/finality and normal UTXO/transaction consensus validation are external tasks after reconstruction",
   "Exactly two legacy transactions, prefilled index0 coinbase<=255bytes, one48bit shortID, one mempool candidate OR one requested missing transaction<=511bytes at differential index1",
   "One structured witness and projections throughout; actual raw transaction bytes SHA256d-bound to the header's full Merkle root, no trusted txid hints; duplicate txids reject",
   "Selector is singleSHA256(header||nonceLE); numericLE keys from first16bytes; SipHash over raw32byte txid, low48bits only; request and response raw blockhashes both bind actualSHA256d(header)",
   "Legacy txid=wtxid profile works for BIP152v1 and this v2 subset; general witness transaction reconstruction and witness commitments are outside this bound",
   "Canonical decoded cmpctblock/request/response input schema; independent local standard-wire encoders/strict decoders roundtrip actual packets and exercise Core differential-index/max/overflow examples; P2P transport parsing and version negotiation remain client boundaries",
   "One-candidate mempool bound has no ambiguity-search path; broader shortID collisions require fallback/fullblock fetch and are not evidence to penalize a peer; two-transaction rejection is reconstruction failure, not consensus-invalidity proof",
   "All8 official Core test procedures inventoried; original randomized three-transaction/preforward/extra-cache procedures not executed or claimed as native upstream vectors; complete fullblock source is original490byte block170",
   "Native Bitcoin environment is unused; budget comparisons do not imply an onchain Bitcoin spend"]
  (boundProgram(blockKernel header))
  [vector "complete actual getblocktxn/blocktxn missing fill" good Accept,
   vector "complete actual one-candidate mempool fill"(make nonce sid 0 cb(R.Mempool transaction))Accept,
   vector "fresh nonce and exact recomputed shortID"(make 0(R.shortId header 0 transaction)0 cb requested)Accept,
   vector "nonce changed without shortID update"(make(nonce+1)sid 0 cb requested)Reject,
   vector "noncanonical64bit shortID highbits"(make nonce(sid+2^48)0 cb requested)Reject,
   vector "wrong prefilled index"(make nonce sid 1 cb requested)Reject,
   vector "actual coinbase bytes changed"(make nonce sid 0(flipFirst cb)requested)Reject,
   vector "actual requested transaction bytes changed"(make nonce sid 0 cb(R.Requested blockHash 1 blockHash(flipFirst transaction)))Reject,
   vector "wrong request raw blockhash"(make nonce sid 0 cb(R.Requested(B.replicate 32 1)1 blockHash transaction))Reject,
   vector "wrong response raw blockhash"(make nonce sid 0 cb(R.Requested blockHash 1(B.replicate 32 2)transaction))Reject,
   vector "wrong missing differential index"(make nonce sid 0 cb(R.Requested blockHash 0 blockHash transaction))Reject,
   vector "wrong actual mempool candidate"(make nonce sid 0 cb(R.Mempool(flipFirst transaction)))Reject,
   vector "duplicate actual transaction IDs"(make nonce(R.shortId header nonce cb)0 cb(R.Mempool cb))Reject])
