-- Diagnostic only: compare actual C/Haskell primitives with a known raw wire.
module Main where
import Control.Monad(unless)
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.Vector as V
import Data.Serialize(runPut)
import Simplicity.Bitcoin.DataTypes
import qualified Simplicity.Bitcoin.Primitive as Prim
import qualified Simplicity.Bitcoin.FFI.Jets as C
import Simplicity.Ty.Word
import JetDiscovery.Tx
import JetDiscovery.Lib.Bytes(w32,w256ToBytes)
import System.Exit(exitFailure)
assert label ok=do putStrLn(label++"="++show ok);unless ok exitFailure
showOp value=case value of
 Just(Right(h,i))->hex(w256ToBytes h)++":"++show(fromWord32 i)
 _->show "failed"
main=do
 let hash=B.pack[0..31]
     op=Outpoint(hashFromBytes hash)0x01020304
     canonical=mkTx 2[mkInput op 1000 BL.empty 0xfffffffe][mkOutput 999(unhex "51")]0
     raw=runPut(putNoWitnessTx canonical)
 parsed<-either fail return(parseRawTx raw)
 let local=rawToSigTx parsed
     former=canonical{sigTxIn=V.map(\input->case sigTxiPreviousOutpoint input of
       Outpoint h i->input{sigTxiPreviousOutpoint=Outpoint(hashFromBytes(B.reverse(hashToBytes h)))i})(sigTxIn canonical)}
     root=hashFromInteger 1
     environment tx=case mkEnv tx 0 defaultTap root of Just e->e;_->error "byteorder environment"
     haskell tx=Prim.primSem Prim.InputPrevOutpoint(toWord32 0)(environment tx)
     cjet tx=C.input_prev_outpoint(environment tx)(toWord32 0)
     bytes value=case value of Just(Right(h,_))->w256ToBytes h;_->B.empty
 putStrLn("raw_wire_hash="++hex hash)
 putStrLn("canonical_Haskell="++showOp(haskell canonical))
 putStrLn("canonical_C_jet="++showOp(cjet canonical))
 putStrLn("local_parsed_Haskell="++showOp(haskell local))
 putStrLn("local_parsed_C_jet="++showOp(cjet local))
 putStrLn("simulated_former_parser_C_jet="++showOp(cjet former))
 assert "canonical primitive preserves exact raw32 bytes"(bytes(haskell canonical)==hash&&bytes(cjet canonical)==hash)
 assert "same SigTx yields equal C and Haskell bytes"(bytes(haskell canonical)==bytes(cjet canonical)&&bytes(haskell local)==bytes(cjet local))
 assert "canonical local parser preserves actual C/Haskell wire primitive"(bytes(haskell local)==hash&&bytes(cjet local)==hash)
 assert "canonical local parser has exact base wire roundtrip"(runPut(putNoWitnessTx local)==raw)
 assert "former reversal regression remains observable in actual C jet"(bytes(cjet former)==B.reverse hash&&bytes(cjet former)/=hash)
 putStrLn("canonical_wire="++hex raw)
 putStrLn("local_base_roundtrip="++hex(runPut(putNoWitnessTx local)))
 upstream<-unhex.filter(/='\n') <$>readFile "vendor-specs/bitcoin-growth2/bip341-group-0-unsigned.hex"
 external<-either fail return(parseRawTx upstream)
 let externalTx=rawToSigTx external
 assert "published BIP341 raw transaction exact canonical base roundtrip"(runPut(putNoWitnessTx externalTx)==upstream)
 assert "published BIP341 first raw outpoint matches actual C/Haskell primitive"(B.index upstream 4<253
   &&bytes(cjet externalTx)==B.take 32(B.drop 5 upstream)&&bytes(haskell externalTx)==B.take 32(B.drop 5 upstream))
