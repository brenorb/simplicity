module Main where
import Control.Monad(unless)
import qualified Data.ByteString as B
import JetDiscovery.Tx
import qualified JetDiscovery.Ref.Bip340 as R
import qualified JetDiscovery.Ref.Bolt12Invoice as Ref
import System.Exit(exitFailure)
fields s=case break(=='\t')s of(a,[])->[a];(a,_:b)->a:fields b
assert label ok=do putStrLn(label++"="++show ok);unless ok exitFailure
main=do
 rows<-map(fields.filter(/='\r')).drop 1.lines <$>readFile "vendor-specs/bitcoin-growth2/bolt12-signature-core.tsv"
 assert "all4 official signature-tree cores present"(length rows==4)
 mapM_(\[idx,raw,root,tag,msg,sig,pk]->do
  tlvs<-either fail return(Ref.parseTlv(unhex raw))
  let actual=Ref.merkle tlvs
  assert("upstream exact Merkle root"++idx)(actual==unhex root)
  if tag=="-"then return()else do
   assert("upstream exact signature digest"++idx)(R.taggedHash tag actual==unhex msg)
   assert("upstream exact BIP340 signature"++idx)(R.verify(unhex pk)(unhex msg)(unhex sig)))rows
 invoices<-map(fields.filter(/='\r')).drop 1.lines <$>readFile "vendor-specs/bitcoin-growth2/bolt12-published-invoice-core.tsv"
 assert "all5 published full invoice transcripts present"(length invoices==5)
 mapM_(\[idx,name,raw]->do
  tlvs<-either fail return(Ref.parseTlv(unhex raw))
  case(lookup 176 tlvs,lookup 240 tlvs)of
   (Just node,Just signature)->assert("published complete invoice signature"++idx++" "++name)(B.length node==33&&R.verify(B.tail node)(Ref.signatureMessage "invoice" tlvs)signature)
   _->assert("missing published invoice auth"++idx)False)invoices
 let paymentHash=hashToBytes(sha256(B.replicate 32 1))
     make created expiry amount maximum features hops=
      let fs=Ref.invoiceFields created expiry paymentHash amount maximum features hops
          sig=R.sign Ref.nodeSecret(Ref.signatureMessage "invoice" fs)(B.replicate 32 0)
      in Ref.invoiceRaw fs sig
     now=1700000600;good=make 1700000000 3600 1000 1000000 2 1
 assert "complete bounded invoice reader policy"(Ref.verifyProfile now good)
 assert "fresh merchant signature cannot violate requested amount"(not(Ref.verifyProfile now(make 1700000000 3600 1001 1000000 2 1)))
 assert "fresh merchant signature cannot authorize expired invoice"(not(Ref.verifyProfile now(make 1699990000 3600 1000 1000000 2 1)))
 assert "unknown even feature rejected with fresh valid signature"(not(Ref.verifyProfile now(make 1700000000 3600 1000 1000000 1 1)))
 assert "nonminimal features rejected with fresh valid signature"(not(Ref.verifyProfile now(make 1700000000 3600 1000 1000000 0 1)))
 assert "zero-hop path rejected with fresh valid signature"(not(Ref.verifyProfile now(make 1700000000 3600 1000 1000000 2 0)))
 assert "no usable path amount limit rejected with fresh valid signature"(not(Ref.verifyProfile now(make 1700000000 3600 1000 999 2 1)))
 writeFile "vendor-specs/bitcoin-growth2/bolt12-derived-invoice.hex"(hex good++"\n")
 writeFile "vendor-specs/bitcoin-growth2/bolt12-derived-invoice.tsv"("kind\tvalue\nclient_supplied_now_utc_seconds\t1700000600\ncreated_utc_seconds\t1700000000\nexpiry_seconds\t3600\namount_msat\t1000\npayment_hash\t"++hex paymentHash++"\nraw_tlv_bytes\t"++show(B.length good)++"\n")
