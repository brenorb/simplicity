"""Reviewed active null-data source model; inspect with the formal reports."""
DECLARATIONS = [
    ('Coq/C/jet_elements_prim.v', 'declaration', 'script', r'''
Definition script := list byte.
'''),
    ('Coq/C/jet_elements_prim.v', 'declaration', 'mapNullDatum', r'''
Definition mapNullDatum {A B : Set} (f : A -> B) (d : txNullDatumF A) : txNullDatumF B :=
  match d with
  | Immediate a => Immediate (f a) | PushData a => PushData (f a)
  | PushData2 a => PushData2 (f a) | PushData4 a => PushData4 (f a)
  | OP1Negate => OP1Negate | OPReserved => OPReserved
  | OP1 => OP1 | OP2 => OP2 | OP3 => OP3 | OP4 => OP4
  | OP5 => OP5 | OP6 => OP6 | OP7 => OP7 | OP8 => OP8
  | OP9 => OP9 | OP10 => OP10 | OP11 => OP11 | OP12 => OP12
  | OP13 => OP13 | OP14 => OP14 | OP15 => OP15 | OP16 => OP16
  end.
'''),
    ('Coq/C/jet_elements_prim.v', 'declaration', 'getBytes', r'''
Definition getBytes (n : Z) (bs : list byte) : option (list byte * list byte) :=
  if Z.leb n (Zlength bs)
  then Some (firstn (Z.to_nat n) bs, skipn (Z.to_nat n) bs)
  else None.
'''),
    ('Coq/C/jet_elements_prim.v', 'declaration', 'leValue', r'''
Fixpoint leValue (bs : list byte) : Z :=
  match bs with
  | [] => 0
  | b :: rest => Byte.unsigned b + 256 * leValue rest
  end.
'''),
    ('Coq/C/jet_elements_prim.v', 'declaration', 'getPush', r'''
Definition getPush (width : Z) (bs : list byte) : option (list byte * list byte) :=
  match getBytes width bs with
  | Some (len, rest) => getBytes (leValue len) rest
  | None => None
  end.
'''),
    ('Coq/C/jet_elements_prim.v', 'declaration', 'getTxNullDatum', r'''
Definition getTxNullDatum (bs : list byte) : option (txNullDatumF (list byte) * list byte) :=
  match bs with
  | [] => None
  | op :: rest =>
      let o := Byte.unsigned op in
      if Z.eqb o 96 then Some (OP16, rest) else
      if Z.eqb o 95 then Some (OP15, rest) else
      if Z.eqb o 94 then Some (OP14, rest) else
      if Z.eqb o 93 then Some (OP13, rest) else
      if Z.eqb o 92 then Some (OP12, rest) else
      if Z.eqb o 91 then Some (OP11, rest) else
      if Z.eqb o 90 then Some (OP10, rest) else
      if Z.eqb o 89 then Some (OP9, rest) else
      if Z.eqb o 88 then Some (OP8, rest) else
      if Z.eqb o 87 then Some (OP7, rest) else
      if Z.eqb o 86 then Some (OP6, rest) else
      if Z.eqb o 85 then Some (OP5, rest) else
      if Z.eqb o 84 then Some (OP4, rest) else
      if Z.eqb o 83 then Some (OP3, rest) else
      if Z.eqb o 82 then Some (OP2, rest) else
      if Z.eqb o 81 then Some (OP1, rest) else
      if Z.eqb o 80 then Some (OPReserved, rest) else
      if Z.eqb o 79 then Some (OP1Negate, rest) else
      if Z.eqb o 78 then option_map (fun p => (PushData4 (fst p), snd p)) (getPush 4 rest) else
      if Z.eqb o 77 then option_map (fun p => (PushData2 (fst p), snd p)) (getPush 2 rest) else
      if Z.eqb o 76 then option_map (fun p => (PushData (fst p), snd p)) (getPush 1 rest) else
      if Z.ltb o 76 then option_map (fun p => (Immediate (fst p), snd p)) (getBytes o rest)
      else None
  end.
'''),
    ('Coq/C/jet_elements_prim.v', 'declaration', 'getTxNullData', r'''
Fixpoint getTxNullData (fuel : nat) (bs : list byte) : option (list (txNullDatumF (list byte))) :=
  match bs with
  | [] => Some []
  | _ :: _ =>
      match fuel with
      | O => None
      | S fuel' =>
          match getTxNullDatum bs with
          | Some (d, rest) => option_map (cons d) (getTxNullData fuel' rest)
          | None => None
          end
      end
  end.
'''),
    ('Coq/C/jet_elements_prim.v', 'declaration', 'txNullData', r'''
Definition txNullData (s : script) : option (list (txNullDatumF (list byte))) :=
  match s with
  | op :: rest => if Z.eqb (Byte.unsigned op) 106 then getTxNullData (length rest) rest else None
  | [] => None
  end.
'''),
    ('Coq/C/jet_elements_prim.v', 'declaration', 'encodeNullDatum', r'''
Let encodeNullDatum (d : txNullDatumF hash256) :
    tySem (Sum (Prod Word2 Word256) (Sum Bit Word4)) :=
match d with
| Immediate h => inl (fromZ 0 : tySem Word2, encodeHash h)
| PushData h => inl (fromZ 1 : tySem Word2, encodeHash h)
| PushData2 h => inl (fromZ 2 : tySem Word2, encodeHash h)
| PushData4 h => inl (fromZ 3 : tySem Word2, encodeHash h)
| OP1Negate => inr (inl (toBit false))
| OPReserved => inr (inl (toBit true))
| OP1 => inr (inr (fromZ 0 : tySem Word4))
| OP2 => inr (inr (fromZ 1 : tySem Word4))
| OP3 => inr (inr (fromZ 2 : tySem Word4))
| OP4 => inr (inr (fromZ 3 : tySem Word4))
| OP5 => inr (inr (fromZ 4 : tySem Word4))
| OP6 => inr (inr (fromZ 5 : tySem Word4))
| OP7 => inr (inr (fromZ 6 : tySem Word4))
| OP8 => inr (inr (fromZ 7 : tySem Word4))
| OP9 => inr (inr (fromZ 8 : tySem Word4))
| OP10 => inr (inr (fromZ 9 : tySem Word4))
| OP11 => inr (inr (fromZ 10 : tySem Word4))
| OP12 => inr (inr (fromZ 11 : tySem Word4))
| OP13 => inr (inr (fromZ 12 : tySem Word4))
| OP14 => inr (inr (fromZ 13 : tySem Word4))
| OP15 => inr (inr (fromZ 14 : tySem Word4))
| OP16 => inr (inr (fromZ 15 : tySem Word4))
end.
'''),
    ('Coq/C/jet_elements_prim.v', 'declaration', 'toBit', r'''
Let toBit (b : bool) : tySem Bit := if b then inr tt else inl tt.
'''),
    ('Coq/C/jet_elements_null_data_parse.v', 'declaration', 'null_data_parse', r'''
Inductive null_data_parse : list byte -> list (txNullDatumF (list byte)) -> Prop :=
| null_data_parse_nil : null_data_parse [] []
| null_data_parse_cons bs d rest ds :
    getTxNullDatum bs = Some (d, rest) -> null_data_parse rest ds -> null_data_parse bs (d :: ds).
'''),
    ('Coq/C/jet_elements_null_data_literal.v', 'declaration', 'haskell_encode_null_datum', r'''
Definition haskell_encode_null_datum (d : txNullDatumF hash256) : Ty.tySem OpcodeTy :=
  match d with
  | Immediate h => inl (haskell_to_word 1 0, haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist h)))
  | PushData h => inl (haskell_to_word 1 1, haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist h)))
  | PushData2 h => inl (haskell_to_word 1 2, haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist h)))
  | PushData4 h => inl (haskell_to_word 1 3, haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist h)))
  | OP1Negate => inr (inl (inl tt))
  | OPReserved => inr (inl (inr tt))
  | OP1 => inr (inr (haskell_to_word 2 0))
  | OP2 => inr (inr (haskell_to_word 2 1))
  | OP3 => inr (inr (haskell_to_word 2 2))
  | OP4 => inr (inr (haskell_to_word 2 3))
  | OP5 => inr (inr (haskell_to_word 2 4))
  | OP6 => inr (inr (haskell_to_word 2 5))
  | OP7 => inr (inr (haskell_to_word 2 6))
  | OP8 => inr (inr (haskell_to_word 2 7))
  | OP9 => inr (inr (haskell_to_word 2 8))
  | OP10 => inr (inr (haskell_to_word 2 9))
  | OP11 => inr (inr (haskell_to_word 2 10))
  | OP12 => inr (inr (haskell_to_word 2 11))
  | OP13 => inr (inr (haskell_to_word 2 12))
  | OP14 => inr (inr (haskell_to_word 2 13))
  | OP15 => inr (inr (haskell_to_word 2 14))
  | OP16 => inr (inr (haskell_to_word 2 15))
  end.
'''),
    ('Coq/C/jet_elements_null_data_literal.v', 'declaration', 'elements_output_null_datum_literal_spec', r'''
Definition elements_output_null_datum_literal_spec (a : Ty.tySem (Ty.Prod Word32 Word32)) (environment : Elements.env) :
    option (Ty.tySem ResultTy) :=
  Some (match hd_error (skipn (Z.to_nat (haskell_from_word 5 (fst a))) (sigTxOut (Elements.envTx environment))) with
        | None => inl tt
        | Some txo =>
            match txNullData (txoScript txo) with
            | None => inl tt
            | Some parsed => inr
                (match hd_error (skipn (Z.to_nat (haskell_from_word 5 (snd a))) parsed) with
                 | None => inl tt
                 | Some d => inr (haskell_encode_null_datum (mapNullDatum byteStringHash d))
                 end)
            end
        end).
'''),
    ('Coq/C/jet_application_context_contract.v', 'declaration', 'application_jet_bitmachine_spec', r'''
Definition application_jet_bitmachine_spec (f : function) (ge : Clight.genv) (E : Set)
    (A B : Ty) (env_rep : mem -> val -> E -> list (block * Z * Z) -> Prop)
    (spec : A -> E -> option B) : Prop :=
  forall logical_env env m L s (a : A) tail fp,
    env_rep m env logical_env fp ->
    Forall (fun '(b, lo, hi) => out_sep (frames_blk L) (item_ofs (active_write_loc L))
      (cells_blk L) (edge_ofs (active_write_loc L)) (Z.of_nat (writeEmpty (activeWriteFrame s)))
      (Z.of_nat (bitSize B)) b lo hi) fp ->
    bm_rep m L s -> bm_separated L s -> active_write_writable m L s ->
    nextData (activeReadFrame s) = @encode A a ++ tail ->
    (bitSize B <= writeEmpty (activeWriteFrame s))%nat ->
    exists mf (value : B),
      spec a logical_env = Some value /\
      Clight2.eval_funcall ge m (Internal f) (jet_args env L) E0 mf (Vint Int.one) /\
      bm_rep mf L
        {| inactiveReadFrames := inactiveReadFrames s;
           activeReadFrame := activeReadFrame s;
           activeWriteFrame :=
             {| writeData := rev (@encode B value) ++ writeData (activeWriteFrame s);
                writeEmpty := (writeEmpty (activeWriteFrame s) - length (@encode B value))%nat |};
           inactiveWriteFrames := inactiveWriteFrames s |}.
'''),
    ('Coq/C/jet_elements_null_data_environment.v', 'declaration', 'elements_null_data_script_flag', r'''
Definition elements_null_data_script_flag (s : script) : bool :=
  match txNullData s with Some _ => true | None => false end.
'''),
    ('Coq/C/jet_elements_null_data_environment.v', 'declaration', 'elements_null_data_opcode_environment', r'''
Definition elements_null_data_opcode_environment m bout outbase k
    (parsed : list (txNullDatumF (list byte))) (fp : list (block * Z * Z)) : Prop :=
  Z.of_nat (length parsed) <= Int64.max_unsigned /\
  Mem.load Mint64 m bout (outbase + 248 * Z.of_nat k + 232) = Some (Vlong (Int64.repr (Z.of_nat (length parsed)))) /\
  forall j d, nth_error parsed j = Some d ->
    exists bop opbase,
      0 <= opbase /\ opbase + 36 * Z.of_nat j + 36 <= Ptrofs.max_unsigned /\
      Mem.load Mptr m bout (outbase + 248 * Z.of_nat k + 224) = Some (Vptr bop (Ptrofs.repr opbase)) /\
      Mem.load Mint32 m bop (opbase + 36 * Z.of_nat j + 32) =
        Some (Vint (elements_datum_code (mapNullDatum byteStringHash d))) /\
      In (bop, opbase + 36 * Z.of_nat j + 32, opbase + 36 * Z.of_nat j + 36) fp /\
      (if elements_datum_push (mapNullDatum byteStringHash d) then
        uint32_array_at m bop (opbase + 36 * Z.of_nat j)
          (hash256_reg (elements_datum_hash (mapNullDatum byteStringHash d) (byteStringHash []))) /\
        In (bop, opbase + 36 * Z.of_nat j, opbase + 36 * Z.of_nat j + 32) fp
       else True).
'''),
    ('Coq/C/jet_elements_null_data_environment.v', 'declaration', 'elements_null_data_output_environment', r'''
Definition elements_null_data_output_environment m bt txbase bout outbase k
    (txo : txOutput) (fp : list (block * Z * Z)) : Prop :=
  0 <= outbase /\ outbase + 248 * Z.of_nat k + 241 <= Ptrofs.max_unsigned /\
  Mem.load Mptr m bt (txbase + 8) = Some (Vptr bout (Ptrofs.repr outbase)) /\
  Mem.load Mint8unsigned m bout (outbase + 248 * Z.of_nat k + 240) =
    Some (Vint (if elements_null_data_script_flag (txoScript txo) then Int.one else Int.zero)) /\
  In (bt, txbase + 8, txbase + 16) fp /\
  In (bout, outbase + 248 * Z.of_nat k + 224, outbase + 248 * Z.of_nat k + 241) fp /\
  match txNullData (txoScript txo) with
  | Some parsed => elements_null_data_opcode_environment m bout outbase k parsed fp
  | None => True
  end.
'''),
    ('Coq/C/jet_elements_null_data_environment.v', 'declaration', 'elements_null_data_environment_rep', r'''
Definition elements_null_data_environment_rep m env (environment : Elements.env) fp : Prop :=
  exists be ebase bt txbase bout outbase,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase /\ ebase + 8 <= Ptrofs.max_unsigned /\
    0 <= txbase /\ txbase + 712 <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be ebase = Some (Vptr bt (Ptrofs.repr txbase)) /\
    Mem.load Mint64 m bt (txbase + 704) =
      Some (Vlong (Int64.repr (Z.of_nat (length (sigTxOut (Elements.envTx environment)))))) /\
    In (be, ebase, ebase + 8) fp /\ In (bt, txbase + 704, txbase + 712) fp /\
    forall k txo, nth_error (sigTxOut (Elements.envTx environment)) k = Some txo ->
      elements_null_data_output_environment m bt txbase bout outbase k txo fp.
'''),
    ('Coq/C/jet_elements_null_data_layout.v', 'declaration', 'elements_output_null_datum_spec', r'''
Definition elements_output_null_datum_spec {alg : Primitive.Algebra} :
    alg (Ty.Prod Word32 Word32) (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit OpcodeTy)) :=
  Primitive.Combinators.prim Elements.OutputNullDatum.
'''),
    ('Coq/C/jet_elements_null_data_parse.v', 'statement', 'getTxNullData_fuel_adequate', r'''
Theorem getTxNullData_fuel_adequate fuel bs ds :
  (length bs <= fuel)%nat -> (getTxNullData fuel bs = Some ds <-> null_data_parse bs ds).
'''),
    ('Coq/C/jet_elements_null_data_parse.v', 'statement', 'txNullData_parser_relation', r'''
Theorem txNullData_parser_relation script ds :
  txNullData script = Some ds <->
  exists op rest, script = op :: rest /\ Byte.unsigned op = 106 /\ null_data_parse rest ds.
'''),
    ('Coq/C/jet_elements_null_data_literal.v', 'statement', 'elements_output_null_datum_literal_bitmachine_spec', r'''
Theorem elements_output_null_datum_literal_bitmachine_spec :
  application_jet_bitmachine_spec f_simplicity_output_null_datum elements_ge Elements.env
    (Ty.Prod Word32 Word32) ResultTy elements_null_data_environment_rep
    elements_output_null_datum_literal_spec.
'''),
    ('Coq/C/jet_elements_null_data_contract.v', 'statement', 'elements_output_null_datum_bitmachine_spec', r'''
Theorem elements_output_null_datum_bitmachine_spec :
  application_jet_bitmachine_spec f_simplicity_output_null_datum elements_ge Elements.env
    (Ty.Prod Word32 Word32)
    (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit (Ty.Sum (Ty.Prod (Word 1) Word256) (Ty.Sum (Ty.Sum Ty.Unit Ty.Unit) (Word 2)))))
    elements_null_data_environment_rep
    (@elements_output_null_datum_spec (PrimitivePrimSem option_Monad_Zero)).
'''),
    ('Coq/C/jet_application_context_transport.v', 'statement', 'application_jet_bitmachine_spec_pointwise', r'''
Lemma application_jet_bitmachine_spec_pointwise f ge (E : Set) (A B : Ty) env_rep (spec literal : A -> E -> option B) :
  (forall a environment, spec a environment = literal a environment) ->
  application_jet_bitmachine_spec f ge E A B env_rep spec ->
  application_jet_bitmachine_spec f ge E A B env_rep literal.
'''),
]
BLOCKS = [
    ('Haskell/Elements/Simplicity/Elements/DataTypes.hs', 'data TxNullDatumF a =', 'getFE ::', r'''
Immediate a
                    | PushData a
                    | PushData2 a
                    | PushData4 a
                    | OP1Negate
                    | OPReserved
                    | OP1
                    | OP2
                    | OP3
                    | OP4
                    | OP5
                    | OP6
                    | OP7
                    | OP8
                    | OP9
                    | OP10
                    | OP11
                    | OP12
                    | OP13
                    | OP14
                    | OP15
                    | OP16
                    deriving (Functor, Foldable, Traversable, Show)

type TxNullDatum = TxNullDatumF BSL.ByteString
type TxNullData = [TxNullDatum]

getTxNullDatum :: Get TxNullDatum
getTxNullDatum = getWord8 >>= go
 where
  go 0x60 = return OP16
  go 0x5f = return OP15
  go 0x5e = return OP14
  go 0x5d = return OP13
  go 0x5c = return OP12
  go 0x5b = return OP11
  go 0x5a = return OP10
  go 0x59 = return OP9
  go 0x58 = return OP8
  go 0x57 = return OP7
  go 0x56 = return OP6
  go 0x55 = return OP5
  go 0x54 = return OP4
  go 0x53 = return OP3
  go 0x52 = return OP2
  go 0x51 = return OP1
  go 0x50 = return OPReserved
  go 0x4f = return OP1Negate
  go 0x4e = do
    n <- getWord32le
    PushData4 <$> getLazyByteString (fromIntegral n)
  go 0x4d = do
    n <- getWord16le
    PushData2 <$> getLazyByteString (fromIntegral n)
  go 0x4c = do
    n <- getWord8
    PushData <$> getLazyByteString (fromIntegral n)
  go op | op < 0x4c = Immediate <$> getLazyByteString (fromIntegral op)
        | otherwise = fail $ "Serialize.get{getTxNullDatum}: " ++ show op ++ "is not a push-data opcode."

txNullData :: Script -> Maybe TxNullData
txNullData = either (const Nothing) Just . runGetLazy prog
 where
  prog = do
    0x6a <- getWord8
    go
  go = do
    emp <- isEmpty
    if emp then return [] else ((:) <$> getTxNullDatum <*> go)
'''),
    ('Haskell/Elements/Simplicity/Elements/Primitive.hs', '  encodeNullDatum (Immediate h) =', '  issuanceAmount =', r'''
Left (toWord2 0, encodeHash h)
  encodeNullDatum (PushData h) = Left (toWord2 1, encodeHash h)
  encodeNullDatum (PushData2 h) = Left (toWord2 2, encodeHash h)
  encodeNullDatum (PushData4 h) = Left (toWord2 3, encodeHash h)
  encodeNullDatum OP1Negate = Right (Left (toBit False))
  encodeNullDatum OPReserved = Right (Left (toBit True))
  encodeNullDatum OP1  = Right (Right (toWord4 0x0))
  encodeNullDatum OP2  = Right (Right (toWord4 0x1))
  encodeNullDatum OP3  = Right (Right (toWord4 0x2))
  encodeNullDatum OP4  = Right (Right (toWord4 0x3))
  encodeNullDatum OP5  = Right (Right (toWord4 0x4))
  encodeNullDatum OP6  = Right (Right (toWord4 0x5))
  encodeNullDatum OP7  = Right (Right (toWord4 0x6))
  encodeNullDatum OP8  = Right (Right (toWord4 0x7))
  encodeNullDatum OP9  = Right (Right (toWord4 0x8))
  encodeNullDatum OP10 = Right (Right (toWord4 0x9))
  encodeNullDatum OP11 = Right (Right (toWord4 0xa))
  encodeNullDatum OP12 = Right (Right (toWord4 0xb))
  encodeNullDatum OP13 = Right (Right (toWord4 0xc))
  encodeNullDatum OP14 = Right (Right (toWord4 0xd))
  encodeNullDatum OP15 = Right (Right (toWord4 0xe))
  encodeNullDatum OP16 = Right (Right (toWord4 0xf))
'''),
    ('Haskell/Elements/Simplicity/Elements/Primitive.hs', '  interpret OutputNullDatum =', '  interpret OutputSurjectionProof =', r'''
\(i, j) -> return . cast $ do
    txo <- lookupOutput . fromInteger $ fromWord32 i
    nullData <- txNullData $ txoScript txo
    return . cast . fmap (encodeNullDatum . fmap bslHash) . listToMaybe $ List.drop (fromInteger (fromWord32 j)) nullData
'''),
    ('Coq/C/jet_elements_prim.v', '| OutputNullDatum => fun ij =>', '| OutputSurjectionProof => atOutput', r'''
let i : Word32 := fst ij in
     let j : Word32 := snd ij in
     Some (cast
       (match nth_error (sigTxOut tx) (Z.to_nat (toZ i)) with
        | Some txo =>
            match txNullData (txoScript txo) with
            | Some nullData =>
                Some (cast (option_map
                  (fun d => encodeNullDatum (mapNullDatum byteStringHash d))
                  (nth_error nullData (Z.to_nat (toZ j)))))
            | None => None
            end
        | None => None
        end))
'''),
    ('C/elements/elementsJets.c', 'bool simplicity_output_null_datum(', 'bool simplicity_output_is_fee(', r'''
frameItem* dst, frameItem src, const txEnv* env) {
  uint_fast32_t i = simplicity_read32(&src);
  if (writeBit(dst, i < env->tx->numOutputs && env->tx->output[i].isNullData)) {
    uint_fast32_t j = simplicity_read32(&src);
    if (writeBit(dst, j < env->tx->output[i].pnd.len)) {
      if (writeBit(dst, OP_PUSHDATA4 < env->tx->output[i].pnd.op[j].code)) {
        skipBits(dst, 2 + 256 - 5);
        if (writeBit(dst, OP_1 <= env->tx->output[i].pnd.op[j].code)) {
          switch (env->tx->output[i].pnd.op[j].code) {
            case OP_1 : writeBit(dst, 0); writeBit(dst, 0); writeBit(dst, 0); writeBit(dst, 0); break;
            case OP_2 : writeBit(dst, 0); writeBit(dst, 0); writeBit(dst, 0); writeBit(dst, 1); break;
            case OP_3 : writeBit(dst, 0); writeBit(dst, 0); writeBit(dst, 1); writeBit(dst, 0); break;
            case OP_4 : writeBit(dst, 0); writeBit(dst, 0); writeBit(dst, 1); writeBit(dst, 1); break;
            case OP_5 : writeBit(dst, 0); writeBit(dst, 1); writeBit(dst, 0); writeBit(dst, 0); break;
            case OP_6 : writeBit(dst, 0); writeBit(dst, 1); writeBit(dst, 0); writeBit(dst, 1); break;
            case OP_7 : writeBit(dst, 0); writeBit(dst, 1); writeBit(dst, 1); writeBit(dst, 0); break;
            case OP_8 : writeBit(dst, 0); writeBit(dst, 1); writeBit(dst, 1); writeBit(dst, 1); break;
            case OP_9 : writeBit(dst, 1); writeBit(dst, 0); writeBit(dst, 0); writeBit(dst, 0); break;
            case OP_10: writeBit(dst, 1); writeBit(dst, 0); writeBit(dst, 0); writeBit(dst, 1); break;
            case OP_11: writeBit(dst, 1); writeBit(dst, 0); writeBit(dst, 1); writeBit(dst, 0); break;
            case OP_12: writeBit(dst, 1); writeBit(dst, 0); writeBit(dst, 1); writeBit(dst, 1); break;
            case OP_13: writeBit(dst, 1); writeBit(dst, 1); writeBit(dst, 0); writeBit(dst, 0); break;
            case OP_14: writeBit(dst, 1); writeBit(dst, 1); writeBit(dst, 0); writeBit(dst, 1); break;
            case OP_15: writeBit(dst, 1); writeBit(dst, 1); writeBit(dst, 1); writeBit(dst, 0); break;
            case OP_16: writeBit(dst, 1); writeBit(dst, 1); writeBit(dst, 1); writeBit(dst, 1); break;
            default: SIMPLICITY_UNREACHABLE;
          }
        } else {
          simplicity_debug_assert(OP_RESERVED == env->tx->output[i].pnd.op[j].code ||
                 OP_1NEGATE == env->tx->output[i].pnd.op[j].code);
          skipBits(dst, 3);
          writeBit(dst, OP_RESERVED == env->tx->output[i].pnd.op[j].code);
        }
      } else {
        switch (env->tx->output[i].pnd.op[j].code) {
          case OP_IMMEDIATE: writeBit(dst, 0); writeBit(dst, 0); break;
          case OP_PUSHDATA: writeBit(dst, 0); writeBit(dst, 1); break;
          case OP_PUSHDATA2: writeBit(dst, 1); writeBit(dst, 0); break;
          case OP_PUSHDATA4: writeBit(dst, 1); writeBit(dst, 1); break;
          default: SIMPLICITY_UNREACHABLE;
        }
        writeHash(dst, &env->tx->output[i].pnd.op[j].dataHash);
      }
    } else {
      skipBits(dst, 1 + 2 + 256);
    }
  } else {
    skipBits(dst, 1 + 1 + 2 + 256);
  }
  return true;
}
'''),
]
LINES = [('Haskell/Simplicity/Elements/Jets.hs',
  'specificationTransaction OutputNullDatum',
  'primitive Prim.OutputNullDatum'),
 ('Haskell/Elements/Simplicity/Elements/Primitive.hs', 'primName OutputNullDatum', '"outputNullDatum"'),
 ('Haskell/Elements/Simplicity/Elements/Primitive.hs', 'lookupOutput', '(sigTxOut tx !?) . fromIntegral')]
FRAGMENTS = [('Haskell/Simplicity/Elements/Jets.hs',
  'OutputNullDatum :: TransactionJet (Word32, Word32) (S (S (Either (Word2, Word256) (Either Bit Word4))))'),
 ('Haskell/Elements/Simplicity/Elements/Primitive.hs',
  'OutputNullDatum :: Prim (Word32, Word32) (S (S (Either (Word2, Word256) (Either Bit Word4))))'),
 ('Haskell/Elements/Simplicity/Elements/DataTypes.hs', 'type Script = BSL.ByteString'),
 ('Coq/C/jet_elements_prim.v',
  '| OutputNullDatum : prim (Prod Word32 Word32) (S (S (Sum (Prod Word2 Word256) (Sum Bit Word4))))'),
 ('Coq/C/jet_elements_prim.v', '| OutputNullDatum => "outputNullDatum"')]

# Dependency origins for Get, qualified List/Vector, and the numeric/hash adapters.
BLOCKS += [
    ('Haskell/Elements/Simplicity/Elements/DataTypes.hs', 'import Control.Monad (', 'just_ f =', r'''
guard, mzero)
import Data.Bits ((.|.))
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import Data.Foldable (toList)
import qualified Data.Map as Map
import Data.Maybe (catMaybes, isJust)
import Data.Semigroup (Max(Max,getMax))
import Data.Serialize ( Serialize, encode
                      , Get, get, runGetLazy, lookAhead, getWord8, getWord16le, getWord32le, getLazyByteString, isEmpty
                      , Putter, put, putWord8, putWord64be, putWord64le, putWord32be, putWord32le, putWord16le, putLazyByteString, runPutLazy
                      )
import Data.String (fromString)
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Word (Word64, Word32, Word16, Word8)
import Lens.Family2 ((&), (.~), (^.), over, review, to, under, view)
import Lens.Family2.Stock (some_)
import Lens.Family2.Unchecked (Adapter, adapter, Traversal)

import Simplicity.Bitcoin
import Simplicity.Digest
import Simplicity.LibSecp256k1.Spec
import Simplicity.LibSecp256k1.Schnorr
import Simplicity.Word
'''),
    ('Haskell/Elements/Simplicity/Elements/Primitive.hs', 'import Control.Arrow (', 'just_ f =', r'''
(***), (+++))
import Control.Monad ((<=<), guard)
import qualified Data.ByteString.Lazy as BSL
import qualified Data.List as List
import Data.Maybe (fromMaybe, listToMaybe)
import qualified Data.Monoid as Monoid
import Data.Serialize (Get, getWord8,
                       Putter, put, putWord8, putWord32be, putWord32le, putWord64le, runPutLazy)
import qualified Data.Word
import Data.Vector as Vector ((!?), length)
import Lens.Family2 (to, view, under)
import Lens.Family2.Stock (some_)

import Simplicity.Digest
import Simplicity.Elements.DataTypes
import qualified Simplicity.LibSecp256k1.Schnorr as Schnorr
import qualified Simplicity.LibSecp256k1.Spec as Schnorr
import Simplicity.Programs.Elements
import Simplicity.Programs.LibSecp256k1
import Simplicity.Serialization
import Simplicity.Ty
import Simplicity.Ty.Bit
import Simplicity.Ty.Word
'''),
]

# Selected byte-string SHA wrapper and its Coq algorithm, not host-library equivalence.
LINES += [('Haskell/Core/Simplicity/Digest.hs', 'bslHash', 'ivHash . IV . pushChunks sha256Incremental . padSHA1')]
DECLARATIONS += [('Coq/Simplicity/Digest.v', 'declaration', 'byteStringHash', r'''
Definition byteStringHash (x : list Integers.byte) : hash256 :=
 Hash256 (process_msg SHA256.init_registers (generate_and_pad_alt x))
  (length_process_msg _).
''')]
