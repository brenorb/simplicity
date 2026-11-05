{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables #-}
-- | Enrolled ES256 WebAuthn wallet with a persistent authenticator counter.
-- Every logical operand enters once; the same fields reach all checks/hashes.
module JetDiscovery.Corpus.WebAuthn
 ( entries, WalletW, walletT, clientHashT, derHashT, authDigestT, referenceAudit ) where
import Prelude hiding (drop,take,not,and,or)
import qualified Prelude as P
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy as BL
import qualified Data.List as L
import Data.Bits (testBit)
import Simplicity.Digest (Hash256)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as A
import qualified Simplicity.Programs.Word as W
import Simplicity.Programs.Sha256.Lib
import Simplicity.Bitcoin.Term (Simplicity,Primitive,primitive)
import qualified Simplicity.Bitcoin.Primitive as Prim
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Ty.Word hiding (Vector)
import JetDiscovery.Corpus.Apps (sigMsg)
import qualified JetDiscovery.Corpus.P256 as P256
import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.State
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.WebAuthn as R

type AuthW=(Word256,(Word8,Word32))
type SigW=((Word256,Word256),(Word256,Buffer127 Word8))
type ClientW=(Buffer511 Word8,Buffer127 Word8)
type AssertionW=(ClientW,(AuthW,SigW))
type WalletW=((Word32,Word64),AssertionW)
type Env=Hash256 -> Maybe Prim.PrimEnv
type Wire=(BS.ByteString,BS.ByteString,BS.ByteString,BS.ByteString)

pick :: (Core t,TyC a,TyC b) => Bool -> t a b -> t (a,a) b
pick True=drop
pick False=take
byteAt :: Core t => Int -> t Word256 Word8
byteAt i=pick(testBit i 4)(pick(testBit i 3)(pick(testBit i 2)(pick(testBit i 1)(pick(testBit i 0)iden))))
bitAt :: Core t => Int -> t Word256 Bit
bitAt i | i>=256=false
        | otherwise=pick(testBit i 7)(pick(testBit i 6)(pick(testBit i 5)(pick(testBit i 4)(pick(testBit i 3)(pick(testBit i 2)(pick(testBit i 1)(pick(testBit i 0)iden)))))))
k8 :: (Core t,TyC a) => Integer -> t a Word8
k8=konst.w8
add8 a b=(a&&&b)>>>A.add word8>>>ih
same a b=(a&&&b)>>>eq>>>verify

-- RFC4648 base64url with no padding. The final sextet has two zero bits.
base64Byte :: Assert t => Int -> t Word256 Word8
base64Byte i=six>>>encode
 where
  b j=bitAt(6*i+j)
  six=((false&&&false)&&&(b 0&&&b 1))&&&((b 2&&&b 3)&&&(b 4&&&b 5))
  less n=(iden&&&k8 n)>>>A.lt word8
  encode=(less 26&&&iden)>>>cond (add8 iden(k8 65))
    ((less 52&&&iden)>>>cond(add8 iden(k8 71))
      ((less 62&&&iden)>>>cond((iden&&&k8 4)>>>A.subtract word8>>>ih)
        (((iden&&&k8 62)>>>eq)&&&iden>>>cond(k8 45)(k8 95))))

appendLiteral :: Assert t => BS.ByteString -> t Ctx8 Ctx8
appendLiteral bs=iden&&&konst(buffer511FromBytes bs)>>>ctx8AddBuffer511
base64Append :: Assert t => t (Ctx8,Word256) Ctx8
base64Append=L.foldl'(>>>)iden[step i|i<-[0..42]]>>>oh
 where step i=((oh&&&(ih>>>base64Byte i))>>>ctx8Add1)&&&ih

-- Exact5.8.1.2 protected prefix, followed by a bounded suffix beginning } or ,.
-- The suffix is hashed in full, as is the separately supplied clientDataJSON.
clientHashT :: Assert t => t (Word256,Buffer127 Word8) Word256
clientHashT=(iden&&&(unit>>>ctx8Init>>>appendLiteral(BSC.pack "{\"type\":\"webauthn.get\",\"challenge\":\"")))>>>
 (oh&&&((ih&&&ooh)>>>base64Append>>>appendLiteral(BSC.pack "\",\"origin\":\"https://wallet.example\",\"crossOrigin\":false")))>>>
 ((ih&&&oih)>>>ctx8AddBuffer buffer127)>>>ctx8Finalize

bufferHead :: Assert t => Buffer Word8 v b -> t b Word8
bufferHead SingleB=verify
bufferHead (DoubleB b)=(oh&&&iden)>>>match(drop ih>>>bufferHead b)(take(W.leftmost(bufferVector b)))

-- Canonical positive ASN.1 INTEGER payload length, including a sign zero.
scalarLen :: Assert t => t Word256 Word8
scalarLen=L.foldr choose lastByte[0..30]
 where
  shape i=((byteAt i>>>W.leftmost word8)&&&unit)>>>cond(k8(toInteger(33-i)))(k8(toInteger(32-i)))
  choose i rest=(((byteAt i&&&k8 0)>>>eq)&&&iden)>>>cond rest(shape i)
  lastByte=shape 31

-- The entire scalar is carried as data; only leading zeros are skipped.
putScalar :: Assert t => t (Ctx8,Word256) Ctx8
putScalar=start>>>L.foldl'(>>>)iden[step i|i<-[0..31]]>>>ioh
 where
  start=ih&&&(((((oh&&&k8 2)>>>ctx8Add1)&&&(ih>>>scalarLen))>>>ctx8Add1)&&&false)
  step i=(skip&&&iden)>>>cond iden putByte
   where
    x=oh>>>byteAt i
    skip=if i==31 then false else and(iih>>>not iden)((x&&&k8 0)>>>eq)
    pad=((x>>>W.leftmost word8)&&&ioh)>>>cond(iden&&&k8 0>>>ctx8Add1)iden
    context=(iih&&&iden)>>>cond ioh pad
    putByte=oh&&&(((context&&&x)>>>ctx8Add1)&&&true)

-- Hash-binding the supplied DER bytes to the canonical serialization of the
-- same r/s used in ECDSA. No trusted decoded-signature or digest hint is used.
derHashT :: Assert t => t (Word256,Word256) Word256
derHashT=(iden&&&header)>>>(oh&&&((ih&&&ooh)>>>putScalar))>>>
 ((ih&&&oih)>>>putScalar)>>>ctx8Finalize
 where
  len=add8(add8(oh>>>scalarLen)(ih>>>scalarLen))(k8 4)
  header=(((unit>>>ctx8Init)&&&k8 0x30)>>>ctx8Add1)&&&len>>>ctx8Add1

authDigestT :: Assert t => t (AuthW,Word256) Word256
authDigestT=((((((unit>>>ctx8Init)&&&ooh)>>>ctx8Add32)&&& (oh>>>ioh))>>>ctx8Add1)&&&(oh>>>iih)>>>ctx8Add4)&&&ih>>>ctx8Add32>>>ctx8Finalize

-- Counter is the low32 bits of the32-byte persistent state.
stateWord :: Core t => t Word32 Word256
stateWord=konst(toWord128 0)&&&(konst(w64 0)&&&(konst(w32 0)&&&iden))
oldCounter :: Core t => t WalletW Word32
oldCounter=ooh
withdrawal :: Core t => t WalletW Word64
withdrawal=oih
client :: Core t => t WalletW (Buffer511 Word8)
client=iooh
suffix :: Core t => t WalletW (Buffer127 Word8)
suffix=ioih
auth :: Core t => t WalletW AuthW
auth=iioh
signature :: Core t => t WalletW SigW
signature=iiih
newCounter :: Core t => t WalletW Word32
newCounter=auth>>>iih
q :: (Integer,Integer)
q=R.publicKey 17

{-# NOINLINE p256Wrapped #-}
p256Wrapped :: J.WrappedSimplicity P256.VerifyInput ()
p256Wrapped=J.jetSubst P256.ecdsaP256T

walletT :: forall t. (Simplicity t,Primitive t) => t WalletW ()
walletT=(iden&&&(client>>>sha256Buffer511))>>>
 ((take policy&&&clientBinding&&&derBinding&&&authorize)>>>unit)
 where
  policy=(loadState(oldCounter>>>stateWord)&&&counterGrows&&&flags&&&rp&&&suffixPolicy&&&outputs)>>>unit
  counterGrows=((oldCounter&&&newCounter)>>>A.lt word32)>>>verify
  flags=same(auth>>>ioh)(k8 5)
  rp=same(auth>>>oh)(konst(w256FromBytes R.rpHash))
  suffixPolicy=let first=suffix>>>bufferHead buffer127 in
    or((first&&&k8 0x7d)>>>eq)((first&&&k8 0x2c)>>>eq)>>>verify
  positive=((konst(w64 0)&&&withdrawal)>>>A.lt word64)>>>verify
  enough=((withdrawal&&&(unit>>>Tx.currentValue))>>>A.lt word64)>>>verify
  remaining=((unit>>>Tx.currentValue)&&&withdrawal)>>>A.subtract word64>>>ih
  outAmount i=konst(w32 i)>>>primitive Prim.OutputValue>>>verify
  outScript i=konst(w32 i)>>>primitive Prim.OutputScriptHash>>>verify
  outputs=(positive&&&enough&&&same(unit>>>Tx.numInputs)(konst(w32 2))&&&same(unit>>>Tx.numOutputs)(konst(w32 2))&&&
    same(outScript 0)(stateScriptHash(newCounter>>>stateWord))&&&same(outAmount 0)remaining&&&same(outAmount 1)withdrawal)>>>unit
  expectedClient=(((unit>>>sigMsg)&&&suffix)>>>clientHashT)
  clientBinding=same ih(take expectedClient)
  actualDer=((unit>>>ctx8Init)&&&(signature>>>iih))>>>ctx8AddBuffer buffer127>>>ctx8Finalize
  expectedDer=signature>>>oh>>>derHashT
  derBinding=take(same actualDer expectedDer)
  z=((take auth&&&ih)>>>authDigestT)
  rs=take(signature>>>oh)
  inv=take(signature>>>ioh)
  key=konst(w256(fst q))&&&konst(w256(snd q))
  authorize=(key&&&(z&&&(rs&&&inv)))>>>J.unwrap p256Wrapped

program :: WalletW -> Prog
program=boundProgram walletT
buf127 b | BS.length b<=127=fst(bufferFill buffer127(map(toWord8.toInteger)(BS.unpack b)))
         | otherwise=error "WebAuthn Buffer127 overflow"
blank :: WalletW
blank=((w32 0,w64 1),((buffer511FromBytes BS.empty,buf127(BSC.pack "}")),((w256 0,(w8 5,w32 1)),((w256 0,w256 0),(w256 0,buf127 BS.empty)))))
{-# NOINLINE walletCmr #-}
walletCmr :: Hash256
walletCmr=progCmr(program blank)
payScript=unhex "0014"<>BS.replicate 20 0x73
feeScript=unhex "0014"<>BS.replicate 20 0x99
walletEnv :: Integer -> Integer -> Integer -> Integer -> BS.ByteString -> Env
walletEnv old next value amount dest cmr=mkEnv transaction 0(\_->stateTap cmr(R.counterState old))cmr
 where
  transaction=mkTx 2
   [mkInput(dummyOutpoint 0)100000(BL.fromStrict(stateScript cmr(R.counterState old)))0xfffffffe,
    mkInput(dummyOutpoint 1)1000(BL.fromStrict feeScript)0xfffffffe]
   [mkOutput(fromInteger value)(stateScript cmr(R.counterState next)),mkOutput(fromInteger amount)dest]0
nativeMessage :: Env -> BS.ByteString
nativeMessage env=case env walletCmr of
 Just e->case J.fastEval(J.unwrap(J.jetSubst sigMsg))e() of Just msg->w256ToBytes msg;_->error "WebAuthn sigAllHash failed"
 _->error "WebAuthn native environment failed"
wireWitness :: Integer -> Integer -> BS.ByteString -> BS.ByteString -> BS.ByteString -> BS.ByteString -> (Integer,Integer) -> WalletW
wireWitness old amount json tailBytes authBytes der rs=
 ((w32 old,w64 amount),((buffer511FromBytes json,buf127 tailBytes),
  ((w256FromBytes(BS.take 32 authBytes),(w8(toInteger(BS.index authBytes 32)),w32(integer(BS.drop 33 authBytes)))),
   ((w256(fst rs),w256(snd rs)),(w256(R.powMod(snd rs)(R.n-2)R.n),buf127 der)))))
 where integer=BS.foldl'(\a b->256*a+toInteger b)0
fixture :: Integer -> Integer -> Env -> BS.ByteString -> (BS.ByteString -> BS.ByteString) -> (BS.ByteString -> BS.ByteString) -> (WalletW,Wire)
fixture old count env tailBytes mutateJson mutateAuth=
 let challenge=nativeMessage env
     json=mutateJson(R.clientData challenge tailBytes)
     a=mutateAuth(R.authData 5 count)
     digest=R.assertionDigest a json
     nonce=1+hashToInteger(sha256(BSC.pack "WebAuthnFixtureNonce"<>digest))`mod`(R.n-1)
     rs=R.signDigest 17 nonce digest;der=R.encodeDer rs
 in (wireWitness old 10000 json tailBytes a der rs,(challenge,json,a,der))

-- Reference-only public fixture/decoder audit, quick enough for normal tests.
referenceAudit :: Bool
referenceAudit=R.selfCheck&&all audit [(17,18,5,True),(17,17,5,False),(17,18,1,False),(2^32-2,2^32-1,5,True)]
 where
  challenge=BS.pack[0..31]
  audit(old,count,flags,expected)=
   let json=R.clientData challenge(BSC.pack "}");a=R.authData flags count
       rs=R.signDigest 17 (100+count) (R.assertionDigest a json)
   in R.verifyAssertion old challenge q json a (R.encodeDer rs)==expected

-- A common fixture list also permits independently checking all signed policy
-- negatives without declaring a rejected covenant to be a signature failure.
fixtureCases :: [(String,Env,WalletW,Wire,Bool)]
fixtureCases=
 [make "counter17 to18" 17 18 (BSC.pack "}") id id True,
  make "counter255 to256, full future field suffix" 255 256 (BSC.pack ",\"futureField\":true}") id id True,
  make "last counter value" (2^32-2) (2^32-1) (BSC.pack "}") id id True,
  make "counter replay" 17 17 (BSC.pack "}") id id False,
  make "counter exhausted" (2^32-1) (2^32-1) (BSC.pack "}") id id False,
  make "wrong RP hash, otherwise valid ECDSA" 17 18 (BSC.pack "}") id (\a->BS.cons 0(BS.drop 1 a)) False,
  make "UV missing, otherwise valid ECDSA" 17 18 (BSC.pack "}") id (\a->BS.take 32 a<>BS.singleton 1<>BS.drop 33 a) False,
  make "crossOrigin true, otherwise valid ECDSA" 17 18 (BSC.pack "}") (\j->BS.take(BS.length j-6)j<>BSC.pack "true}") id False,
  make "wrong challenge, otherwise valid ECDSA" 17 18 (BSC.pack "}") (\j->BS.take 36 j<>BS.singleton(if BS.index j 36==65 then 66 else 65)<>BS.drop 37 j) id False]
 where
  make name old count tailBytes mj ma expected=
   let env=walletEnv old count 90000 10000 payScript;(w,wire)=fixture old count env tailBytes mj ma
   in(name,env,w,wire,expected)

entries :: [Entry]
entries=[Entry "app-webauthn-counter-wallet" "WebAuthn ES256 wallet with transaction challenge, counter state and native withdrawal"
 "W3C WebAuthn Level2 2021-04-08 sections5.8.1.2,6.1,7.2; FIPS186-5 P256 ECDSA; vendor-specs/crypto-growth/webauthn-2.html"
 BitcoinApp(Derived "independent Integer P256 signer/reference checked against RFC6979 sample; exact wire DER, RP/authenticator/client data, native sig_all_hash and genuine state-committed funding")
 ["pre-enrolled fixed ES256 credential/RP wallet.example/origin https://wallet.example; credential registration, attestation chains, TLS/token-binding and authenticator extensions are outside this spending profile",
  "counter-capable authenticator: strict monotone unsigned32 counter, UP+UV exactly0x05 and37-byte authenticatorData; no always-zero counters; maximum counter exhausts this profile",
  "published limited clientDataJSON prefix algorithm; complete trailing suffix1..127 bytes starts } or ,; all suffix bytes are hashed; recipient/withdrawal/continuation are bound by actual sig_all_hash",
  "canonical DER is hash-bound to the same typed r/s used in ECDSA, under SHA256 collision resistance; decoded hints cannot replace the native digest; each logical witness enters once",
  "one wallet input plus one independently authorized fee input, exactly2outputs, positive withdrawal with nonzero continuing reserve; continuation commits new counter and the same single executable leaf"]
 program (baseVectors++extraVectors)]
 where
  baseVectors=[Vector name env w(if expected then Accept else Reject)|(name,env,w,_,expected)<-fixtureCases]
  goodEnv=walletEnv 17 18 90000 10000 payScript
  (good,_)=fixture 17 18 goodEnv(BSC.pack "}")id id
  remapSig f ((a,b),(c,(d,s)))=((a,b),(c,(d,f s)))
  badDER ((r,s),(inv,_))=((r,s),(inv,buf127 malformed))
   where
    der=R.encodeDer(toInteger(fromWord256 r),toInteger(fromWord256 s))
    malformed=BS.pack[0x30,BS.index der 1+1,2,BS.index der 3+1,0]<>BS.drop 4 der
  extraVectors=
   [Vector "different transaction with original assertion" (walletEnv 17 18 90000 10000 feeScript) good Reject,
    Vector "old counter opening splice" goodEnv ((w32 16,snd(fst good)),snd good) Reject,
    Vector "suffix hint splice" goodEnv (let (h,((j,_),a))=good in(h,((j,buf127(BSC.pack ",\"fake\":true}")),a))) Reject,
    Vector "nonminimal DER leading zero, canonical scalars otherwise" goodEnv (remapSig badDER good) Reject,
    Vector "inverse hint splice" goodEnv(remapSig(\(rs,(_,der))->(rs,(w256 1,der)))good) Reject,
    signedBad "continuation counter not advanced" (walletEnv 17 17 90000 10000 payScript),
    signedBad "continuation collateral reduced" (walletEnv 17 18 89999 10000 payScript),
    signedBad "withdrawal amount differs" (walletEnv 17 18 90000 9999 payScript)]
  signedBad name env=let(w,_)=fixture 17 18 env(BSC.pack "}")id id in Vector name env w Reject
