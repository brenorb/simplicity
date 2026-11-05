module Main where
import Control.Monad(unless)
import qualified Data.ByteString as B
import qualified JetDiscovery.Ref.CompactBlock as R
import JetDiscovery.Tx
import JetDiscovery.Ref.BitcoinGrowth(sha256d)
import System.Exit(exitFailure)
fields s=case break(=='\t')s of(a,[])->[a];(a,_:b)->a:fields b
assert label ok=do putStrLn(label++"="++show ok);unless ok exitFailure
main=do
 rows<-map fields.drop 1.lines <$>readFile "vendor-specs/bitcoin-growth5/bip152-historical-fixture.tsv"
 let field name=case[v|[k,v]<-rows,k==name]of[v]->v;_->error name
     header=unhex(field "header_raw");cb=unhex(field "coinbase_raw");transaction=unhex(field "transaction_raw")
     blockHash=sha256d header;nonce=read(field "compact_nonce");sid=R.shortId header nonce transaction
     compact=R.compactEncode header nonce sid 0 cb
     request=R.requestEncode blockHash[1];response=R.responseEncode blockHash transaction
     values=[0,1,3,4]
 assert "actual raw header/transaction/Merkle hashes"(blockHash==unhex(field "block_hash_raw")&&sha256d cb==unhex(field "coinbase_txid_raw")&&sha256d transaction==unhex(field "transaction_txid_raw")&&sha256d(sha256d cb<>sha256d transaction)==B.take 32(B.drop 36 header))
 assert "complete canonical cmpctblock wire roundtrip"(R.compactDecode compact==Just(header,nonce,sid,0,cb))
 assert "complete canonical getblocktxn wire roundtrip"(R.requestDecode request==Just(blockHash,[1]))
 assert "complete canonical blocktxn wire roundtrip"(R.responseDecode response==Just(blockHash,transaction))
 assert "complete actual mempool reconstruction"(R.verify header nonce sid 0 cb(R.Mempool transaction))
 assert "complete actual requested reconstruction"(R.verify header nonce sid 0 cb(R.Requested blockHash 1 blockHash transaction))
 assert "published Core request differential index example"(R.requestDecode(R.requestEncode blockHash values)==Just(blockHash,values))
 assert "published Core maximum index65535"(R.requestDecode(R.requestEncode blockHash[65535])==Just(blockHash,[65535]))
 let overflow=blockHash<>R.compactSize 3<>R.compactSize 0x7000<>R.compactSize(0x10000-0x7000-2)<>R.compactSize 0
 assert "published Core original overflow deltas rejected"(R.requestDecode overflow==Nothing)
 assert "nonminimal request CompactSize rejected"(R.requestDecode(blockHash<>unhex "fd010001")==Nothing)
 assert "wrong response count rejected"(R.responseDecode(blockHash<>B.singleton 2<>transaction)==Nothing)
 assert "wrong prefilled transaction count rejected"(R.compactDecode(B.take 95 compact<>B.singleton 2<>B.drop 96 compact)==Nothing)
 writeFile "vendor-specs/bitcoin-growth5/bip152-derived-wire.tsv"("kind\traw_bytes\n"++concat[k++"\t"++hex b++"\n"|(k,b)<-[("cmpctblock",compact),("getblocktxn",request),("blocktxn",response)]])
 writeFile "vendor-specs/bitcoin-growth5/bip152-derived-shortid.tsv"("nonce\tkey0_numeric_le\tkey1_numeric_le\tshortid48_numeric\n"++show nonce++"\t"++show(fst(R.keys header nonce))++"\t"++show(snd(R.keys header nonce))++"\t"++show sid++"\n")
