module Main where
import Control.Monad(unless)
import qualified Data.ByteString as B
import JetDiscovery.Tx
import qualified JetDiscovery.Ref.Bip340 as R
import qualified JetDiscovery.Ref.SilentPayment as K
import System.Exit(exitFailure)
fields s=case break(=='\t')s of(a,[])->[a];(a,_:b)->a:fields b
assert label ok=do putStrLn(label++"="++show ok);unless ok exitFailure
main=do
 valid<-map fields.drop 1.lines <$>readFile "vendor-specs/bitcoin-growth6/bip32-all-valid.tsv"
 assert "all17published valid private/public pairs present"(length valid==17)
 mapM_(\row->case row of
  [group,path,_,_,public,private,_,_,_]->assert("source"++group++" "++path++" exact full compressed public/private relation")
    (K.compressed(R.pointMul R.gPt(R.intFromBytes(unhex private)))==unhex public)
  _->fail "BIP32 valid columns")valid
 public<-map fields.drop 1.lines <$>readFile "vendor-specs/bitcoin-growth6/bip32-public-ckd-vectors.tsv"
 assert "all6published nonhardened public derivation edges present"(length public==6)
 mapM_(\row->case row of
  [group,path,parent,_,index,il,ir,expected,chain,_,_]->do
   let point=R.pointAdd(K.decodeCompressed(unhex parent))(R.pointMul R.gPt(R.intFromBytes(unhex il)))
   assert("source"++group++" "++path++" exact CKDpub point/chain")
    (read index<2^31&&R.intFromBytes(unhex il)<R.n&&K.compressed point==unhex expected&&ir==chain)
  _->fail "BIP32 public columns")public
