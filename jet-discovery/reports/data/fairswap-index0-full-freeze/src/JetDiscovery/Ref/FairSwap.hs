-- | Independent bounded FairSwap file circuit and complaint reference.
-- Author thesis chapter5 Algorithm8 plus fixed file-sale wiring. No imported
-- Solidity/Rust code is executed. Protocol paths and native deadline caveat are
-- recorded in reports/FAIRSWAP-NATIVE-SCOPE.md.
module JetDiscovery.Ref.FairSwap
 ( Header,Opening,Gate,plainNodes,cipherNodes,cipherTree,opening,header
 , crypt,verifyOpening,rootComplaint,gateComplaint,stateBytes,audit ) where
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import Data.Bits(xor,testBit,shiftR)
import Data.List(foldl')
import Data.Word(Word8)
import JetDiscovery.Ref.Keccak(keccak256)
import JetDiscovery.Tx(sha256,hashToBytes)
type Header=(B.ByteString,(B.ByteString,B.ByteString))
type Opening=(B.ByteString,[B.ByteString])
type Gate=(Opening,(Opening,Opening))
word32 :: Integer -> B.ByteString
word32 n=B.pack[fromIntegral(n`shiftR`(8*i))|i<-[31,30..0]]
validWord :: B.ByteString -> Bool
validWord x=B.length x==32
plainNodes :: [B.ByteString] -> [B.ByteString]
plainNodes chunks
 |length chunks/=4||not(all validWord chunks)=error "FairSwap requires4chunks of32bytes"
 |otherwise=chunks++[a,b,keccak256(a<>b)]
 where a=keccak256(chunks!!0<>chunks!!1);b=keccak256(chunks!!2<>chunks!!3)
crypt :: B.ByteString -> Int -> B.ByteString -> B.ByteString
crypt key i value
 |not(validWord key&&validWord value)||i<0||i>6=error "FairSwap word/index bound"
 |otherwise=B.pack(B.zipWith xor value(keccak256(word32(toInteger domain)<>key)))
 where domain=if i<4 then i else 4+i
cipherNodes :: B.ByteString -> [B.ByteString] -> [B.ByteString]
cipherNodes key chunks=zipWith(crypt key)[0..](plainNodes chunks)
leaves cs
 |length cs/=7||not(all validWord cs)=error "FairSwap ciphertext dimension"
 |otherwise=map keccak256(take 4 cs)++drop 4 cs++[B.replicate 32 0]
parents []=[]
parents(a:b:xs)=keccak256(a<>b):parents xs
parents _=error "FairSwap tree level must be even"
levels cs=take 4(iterate parents(leaves cs))
cipherTree :: [B.ByteString] -> B.ByteString
cipherTree cs=head(last(levels cs))
opening :: [B.ByteString] -> Int -> Opening
opening cs i
 |i<0||i>6=error "FairSwap opening index"
 |otherwise=(cs!!i,[levels cs!!j!!((i`div`2^j)`xor`1)|j<-[0..2]])
header :: B.ByteString -> [B.ByteString] -> Header
header key chunks=(keccak256 key,(cipherTree(cipherNodes key chunks),last(plainNodes chunks)))
verifyOpening :: B.ByteString -> Int -> Opening -> Bool
verifyOpening root i(c,siblings)=i>=0&&i<=6&&validWord c&&length siblings==3&&all validWord siblings&&
 foldl' step(if i<4 then keccak256 c else c)(zip[0..]siblings)==root
 where step node(j,s)=if testBit i j then keccak256(s<>node)else keccak256(node<>s)
rootComplaint :: Header -> B.ByteString -> Opening -> Bool
rootComplaint (commit,(root,fileRoot)) key o@(c,_)=keccak256 key==commit&&verifyOpening root 6 o&&crypt key 6 c/=fileRoot
gateComplaint :: Header -> B.ByteString -> Int -> Int -> Int -> Gate -> Bool
gateComplaint (commit,(root,_)) key out left right(o,(a,b))=
 keccak256 key==commit&&all(uncurry(verifyOpening root))[(out,o),(left,a),(right,b)]&&
 crypt key out(fst o)/=keccak256(crypt key left(fst a)<>crypt key right(fst b))
stateBytes :: Word8 -> Header -> B.ByteString -> B.ByteString
stateBytes phase(commit,(root,fileRoot))key=hashToBytes(sha256(C.pack "FairSwapNativeV1"<>B.singleton phase<>commit<>root<>fileRoot<>key))
-- Includes a concrete false-complaint certificate if valid gate wiring is
-- omitted: honest output4 is compared against the unrelated plaintext2/3.
audit :: Bool
audit=and
 [all(\i->verifyOpening root i(opening cs i))[0..6]
 ,not(rootComplaint h key(opening cs 6))
 ,and[not(gateComplaint h key out a b(opening cs out,(opening cs a,opening cs b)))|(out,a,b)<-[(4,0,1),(5,2,3),(6,4,5)]]
 ,gateComplaint h key 4 2 3(opening cs 4,(opening cs 2,opening cs 3))
 ,rootComplaint badHeader key(opening bad 6)
 ,not(verifyOpening root 5(opening cs 4))]
 where
  key=word32 991;chunks=[word32 i|i<-[10..13]];cs=cipherNodes key chunks
  h=header key chunks;root=cipherTree cs
  bad=take 6 cs++[B.pack(B.zipWith xor(cs!!6)(word32 1))]
  badHeader=(keccak256 key,(cipherTree bad,last(plainNodes chunks)))
