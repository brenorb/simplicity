-- | Independent Integer/bytes reference for the bounded WebAuthn wallet profile.
-- Test signing is deterministic fixture tooling, not production key management.
module JetDiscovery.Ref.WebAuthn
 ( p,n,g,Point,add,mul,powMod,publicKey,signDigest,verifyDigest
 , rpId,origin,rpHash,clientPrefix,clientData,authData,assertionDigest
 , base64url,encodeDer,decodeDer,verifyAssertion,counterState,selfCheck
 ) where
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import Data.Bits (shiftR,testBit,(.&.))
import Data.Word (Word8)
import JetDiscovery.Tx (sha256,hashToBytes,unhex)

p,n :: Integer
p=0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
n=0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
type Point=Maybe (Integer,Integer)
g :: Point
g=Just (0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296,
        0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5)
powMod :: Integer -> Integer -> Integer -> Integer
powMod _ 0 m=1 `mod`m
powMod b e m | even e=let h=powMod b (e`div`2) m in h*h`mod`m
             | otherwise=b*powMod b (e-1) m`mod`m
add :: Point -> Point -> Point
add Nothing q=q
add q Nothing=q
add (Just (x,y)) (Just (u,v))
 | x==u && (y/=v || y==0)=Nothing
 | otherwise=Just (a,(s*(x-a)-y)`mod`p)
 where
  s=if x==u then (3*x*x-3)*powMod (2*y) (p-2) p`mod`p
            else (v-y)*powMod (u-x) (p-2) p`mod`p
  a=(s*s-x-u)`mod`p
mul :: Point -> Integer -> Point
mul q k=go q k Nothing
 where go _ 0 acc=acc
       go b e acc=go (add b b) (e`shiftR`1) (if testBit e 0 then add acc b else acc)
publicKey :: Integer -> (Integer,Integer)
publicKey sk=case mul g sk of Just q->q;Nothing->error "invalid P256 secret"
integer=BS.foldl' (\a b->256*a+toInteger b) 0
bytesN len x=BS.pack [fromIntegral(x`shiftR`(8*i))|i<-[len-1,len-2..0]]
hash=hashToBytes.sha256
signDigest :: Integer -> Integer -> BS.ByteString -> (Integer,Integer)
signDigest sk nonce digest
 | sk<=0 || sk>=n || nonce<=0 || nonce>=n || BS.length digest/=32=error "bad fixture signer input"
 | otherwise=case mul g nonce of
    Just(x,_)->let r=x`mod`n;s=(powMod nonce (n-2)n*(integer digest+r*sk))`mod`n
               in if r==0 || s==0 then error "fixture nonce generated zero scalar" else (r,s)
    Nothing->error "zero fixture nonce"
verifyDigest :: (Integer,Integer) -> BS.ByteString -> (Integer,Integer) -> Bool
verifyDigest (x,y) digest (r,s)
 | x<0 || x>=p || y<0 || y>=p || (y*y-x*x*x+3*x-0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B)`mod`p/=0=False
 | BS.length digest/=32 || r<=0 || r>=n || s<=0 || s>=n=False
 | otherwise=case add (mul g (integer digest*w`mod`n)) (mul (Just(x,y)) (r*w`mod`n)) of
    Just(a,_)->a`mod`n==r;Nothing->False
 where w=powMod s (n-2)n

rpId,origin :: BS.ByteString
rpId=BSC.pack "wallet.example"
origin=BSC.pack "https://wallet.example"
rpHash=hash rpId
base64url :: BS.ByteString -> BS.ByteString
base64url input=BS.pack (go(BS.unpack input))
 where
  alphabet=BSC.pack "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"
  at x=BS.index alphabet (fromIntegral x)
  go(a:b:c:xs)=[at(a`shiftR`2),at(((a.&.3)*16)+(b`shiftR`4)),at(((b.&.15)*4)+(c`shiftR`6)),at(c.&.63)]++go xs
  go[a,b]=[at(a`shiftR`2),at(((a.&.3)*16)+(b`shiftR`4)),at((b.&.15)*4)]
  go[a]=[at(a`shiftR`2),at((a.&.3)*16)]
  go[]=[]
clientPrefix :: BS.ByteString -> BS.ByteString
clientPrefix challenge=BSC.pack "{\"type\":\"webauthn.get\",\"challenge\":\""<>base64url challenge<>
 BSC.pack "\",\"origin\":\"https://wallet.example\",\"crossOrigin\":false"
clientData :: BS.ByteString -> BS.ByteString -> BS.ByteString
clientData challenge tailBytes=clientPrefix challenge<>tailBytes
authData :: Word8 -> Integer -> BS.ByteString
authData flags count=rpHash<>BS.singleton flags<>bytesN 4 count
assertionDigest :: BS.ByteString -> BS.ByteString -> BS.ByteString
assertionDigest auth json=hash(auth<>hash json)
counterState :: Integer -> BS.ByteString
counterState count=BS.replicate 28 0<>bytesN 4 count

-- Strict short-form ASN.1 DER; all valid P256 scalar lengths1..33 supported.
encodeDer (r,s)=BS.pack[0x30,fromIntegral(BS.length body)]<>body
 where
  enc x=let raw=BS.dropWhile(==0)(bytesN 32 x)
            mag=if BS.null raw then BS.singleton 0 else raw
            pos=if BS.head mag>=128 then BS.cons 0 mag else mag
         in BS.pack[2,fromIntegral(BS.length pos)]<>pos
  body=enc r<>enc s
decodeDer :: BS.ByteString -> Maybe (Integer,Integer)
decodeDer bs
 | BS.length bs<8 || BS.length bs>72 || BS.index bs 0/=0x30 || fromIntegral(BS.index bs 1)/=BS.length bs-2=Nothing
 | otherwise=do
    (r,rest)<-one(BS.drop 2 bs);(s,end)<-one rest
    if BS.null end && r>0 && r<n && s>0 && s<n then Just(r,s) else Nothing
 where
  one x
   | BS.length x<3 || BS.head x/=2=Nothing
   | len<1 || len>33 || BS.length x<2+len=Nothing
   | BS.head mag>=128=Nothing
   | len>1 && BS.head mag==0 && BS.index mag 1<128=Nothing
   | otherwise=Just(integer mag,BS.drop(2+len)x)
   where len=fromIntegral(BS.index x 1);mag=BS.take len(BS.drop 2 x)

-- Counter-capable, no-extension, pre-enrolled ES256 profile. Fixed policy
-- requires UP+UV; authenticators with an always-zero counter are unsupported.
verifyAssertion :: Integer -> BS.ByteString -> (Integer,Integer) -> BS.ByteString -> BS.ByteString -> BS.ByteString -> Bool
verifyAssertion old challenge q json auth der
 | old<0 || old>=2^(32::Int) || BS.length challenge/=32=False
 | BS.length auth/=37 || BS.take 32 auth/=rpHash || BS.index auth 32/=5=False
 | count<=old=False
 | not(BS.isPrefixOf prefix json) || BS.length tailBytes<1 || BS.length tailBytes>127=False
 | BS.head tailBytes/=0x7d && BS.head tailBytes/=0x2c=False
 | otherwise=case decodeDer der of Just rs->verifyDigest q (assertionDigest auth json) rs;Nothing->False
 where
  count=integer(BS.drop 33 auth)
  prefix=clientPrefix challenge
  tailBytes=BS.drop(BS.length prefix)json

selfCheck :: Bool
selfCheck=verifyDigest q (hash(BSC.pack "sample")) rs
 && base64url(BS.pack[0..31])==BSC.pack "AAECAwQFBgcICQoLDA0ODxAREhMUFRYXGBkaGxwdHh8"
 && all (\x->decodeDer(encodeDer x)==Just x) [(1,1),(127,128),(255,256),(n-1,n-2)]
 && all ((==Nothing).decodeDer.unhex) ["3006020100020101","300702020001020101","3006020180020101","300602010102010100"]
 where
  q=(0x60FED4BA255A9D31C961EB74C6356D68C049B8923B61FA6CE669622E60F29FB6,0x7903FE1008B8BC99A41AE9E95628BC64F2F1B20C2D7E9F5177A3C294D4462299)
  rs=(0xEFD48B2AACB6A8FD1140DD9CD45E81D69D2C877B56AAF991C34D0EA84EAF3716,0xF7CB1C942D657C41D436C7A1B6E29F65F3E900DBB9AFF4064DC4AB2F843ACDA8)
