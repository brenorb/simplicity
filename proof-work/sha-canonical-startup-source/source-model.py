"""Fixed reviewed SHA compression/context/Bitcoin/startup source boundary.

Initial capture plus additive transitive word/bit/padding/order/type helpers.
Do not regenerate from changed candidates to make a failing gate pass.
See README.md for correspondence and host-library limits.
"""
MODEL = {'declarations': [['Coq/Simplicity/SHA256.v',
                   'declaration',
                   'scribe32',
                   'Definition scribe32 (z : Z) {A} {term : Core.Algebra} : term A Word32 :=\n'
                   ' scribe (fromZ z).\n'],
                  ['Coq/Simplicity/SHA256.v',
                   'declaration',
                   'add32',
                   'Definition add32 {term : Core.Algebra} : term (Word32 * Word32) Word32 := adder >>> I '
                   'H.\n'],
                  ['Coq/Simplicity/SHA256.v',
                   'declaration',
                   'xor3Word32',
                   'Definition xor3Word32 {term : Core.Algebra} : term (Word32 * (Word32 * Word32)) Word32 '
                   ':= \n'
                   '  bitwiseTri xor3.\n'],
                  ['Coq/Simplicity/SHA256.v',
                   'declaration',
                   'chWord32',
                   'Definition chWord32 {term : Core.Algebra} : term (Word32 * (Word32 * Word32)) Word32 '
                   ':= \n'
                   '  bitwiseTri ch.\n'],
                  ['Coq/Simplicity/SHA256.v',
                   'declaration',
                   'majWord32',
                   'Definition majWord32 {term : Core.Algebra} : term (Word32 * (Word32 * Word32)) Word32 '
                   ':= \n'
                   '  bitwiseTri maj.\n'],
                  ['Coq/Simplicity/SHA256.v',
                   'declaration',
                   'shift32',
                   'Definition shift32 z {term : Core.Algebra} : term Word32 Word32 := \n  shift_const z.\n'],
                  ['Coq/Simplicity/SHA256.v',
                   'declaration',
                   'rotate32',
                   'Definition rotate32 z {term : Core.Algebra} : term Word32 Word32 := \n'
                   '  rotate_const z.\n'],
                  ['Coq/Simplicity/SHA256.v',
                   'declaration',
                   'hashBlock',
                   'Definition hashBlock {term : Core.Algebra} : term (Word256 * Word512) Word256 :=\n'
                   'let a32 := add32 in\n'
                   'let x32 := xor3Word32 in\n'
                   'let diag := O I H &&& I O H in\n'
                   'let odiag := O diag in\n'
                   'let idiag := I diag in\n'
                   'let bigDiag := O I I H &&& I O O H in\n'
                   'let part1Schedule := odiag &&& bigDiag in\n'
                   'let smallSigma0 := rotate32 (-7) &&& rotate32 (-18) &&& shift32 (-3) >>> x32 in\n'
                   'let smallSigma1 := rotate32 (-17) &&& rotate32 (-19) &&& shift32 (-10) >>> x32 in\n'
                   'let smallSigma := (O O O (O H &&& (I H >>> smallSigma0)) >>> a32)\n'
                   '             &&& (I (O O I H &&& (I I O H >>> smallSigma1)) >>> a32) >>> a32 in\n'
                   'let schedule := (O part1Schedule &&& (O idiag &&& (O I I I H &&& I (O O O H))))\n'
                   '           &&& (I part1Schedule &&& (I idiag &&& (I I I I H &&& smallSigma))) in\n'
                   'let bigSigma0 := rotate32 (-2) &&& rotate32 (-13) &&& rotate32 (-22) >>> x32 in\n'
                   'let bigSigma1 := rotate32 (-6) &&& rotate32 (-11) &&& rotate32 (-25) >>> x32 in\n'
                   'let t1 := (O H &&& I I O O O O H >>> a32) &&& I O (I (I I H &&& ((O O H >>> bigSigma1) '
                   '&&& (O O H &&& diag >>> chWord32) >>> a32)) >>> a32) >>> a32 in\n'
                   'let t12 := O ((O I H &&& I H >>> majWord32) &&& (O (O H &&& (I H >>> bigSigma0)) >>> '
                   'a32)) >>> a32 in\n'
                   'let t1d := O O O H &&& I O O H >>> a32 in\n'
                   'let part1Round := ((t1 &&& I O O O O H) &&& I O odiag)\n'
                   '             &&& I O (bigDiag &&& idiag) in\n'
                   'let part2Round := ((t12 &&& O O I H) &&& O I H)\n'
                   '              &&& ((t1d &&& I O I H) &&& I I H) in\n'
                   'let round := part1Round >>> part2Round in\n'
                   'let step := round &&& I I schedule in\n'
                   'let k0 := 1116352408%Z in\n'
                   'let ks :=    [ 1899447441; 3049323471; 3921009573;\n'
                   '   961987163 ; 1508970993; 2453635748; 2870763221;\n'
                   '   3624381080;  310598401;  607225278; 1426881987;\n'
                   '   1925078388; 2162078206; 2614888103; 3248222580;\n'
                   '   3835390401; 4022224774;  264347078;  604807628;\n'
                   '    770255983; 1249150122; 1555081692; 1996064986;\n'
                   '   2554220882; 2821834349; 2952996808; 3210313671;\n'
                   '   3336571891; 3584528711;  113926993;  338241895;\n'
                   '    666307205;  773529912; 1294757372; 1396182291;\n'
                   '   1695183700; 1986661051; 2177026350; 2456956037;\n'
                   '   2730485921; 2820302411; 3259730800; 3345764771;\n'
                   '   3516065817; 3600352804; 4094571909;  275423344;\n'
                   '    430227734;  506948616;  659060556;  883997877;\n'
                   '    958139571; 1322822218; 1537002063; 1747873779;\n'
                   '   1955562222; 2024104815; 2227730452; 2361852424;\n'
                   '   2428436474; 2756734187; 3204031479; 3329325298]%Z in\n'
                   'let compression := scribe32 k0 &&& iden >>> fold_right (fun k (rec : term (Word32 * '
                   '(Word256 * Word512)) Word256) => scribe32 k &&& step >>> rec) round ks in\n'
                   'let collate (x : term Word256 Word32) := O x &&& I x >>> a32 in\n'
                   '  O H &&& compression >>>\n'
                   '    ((collate (O O O H) &&& collate (O O I H)) &&&\n'
                   '     (collate (O I O H) &&& collate (O I I H))) &&&\n'
                   '    ((collate (I O O H) &&& collate (I O I H)) &&&\n'
                   '     (collate (I I O H) &&& collate (I I I H))).\n'],
                  ['Coq/Simplicity/Word.v',
                   'declaration',
                   'zero',
                   'Fixpoint zero {n : nat} {term : Core.Algebra} : term Unit (Word n) :=\n'
                   'match n with\n'
                   '| 0 => false\n'
                   '| S n => zero &&& zero\n'
                   'end.\n'],
                  ['Coq/Simplicity/Word.v',
                   'declaration',
                   'adderBit',
                   'Definition adderBit {term : Core.Algebra} : term (Bit * Bit) (Bit * Bit) :=\n'
                   '  cond (iden &&& not iden) (false &&& iden).\n'],
                  ['Coq/Simplicity/Word.v',
                   'declaration',
                   'fullAdderBit',
                   'Definition fullAdderBit {term : Core.Algebra} : term (Bit * (Bit * Bit)) (Bit * Bit) :=\n'
                   '  maj &&& xor3.\n'],
                  ['Coq/Simplicity/Word.v',
                   'declaration',
                   'buildFullAdder',
                   'Definition buildFullAdder {W} {term : Core.Algebra} (rec : term (Bit * (W * W)) (Bit * '
                   'W)) :\n'
                   '  term (Bit * ((W * W) * (W * W))) (Bit * (W * W)) :=\n'
                   '    drop (O O H &&& I O H) &&& (O H &&& drop (O I H &&& I I H) >>> rec)\n'
                   '>>> I I H &&& (I O H &&& O H >>> rec)\n'
                   '>>> I O H &&& (I I H &&& O H).\n'],
                  ['Coq/Simplicity/Word.v',
                   'declaration',
                   'fullAdder',
                   'Fixpoint fullAdder {n : nat} {term : Core.Algebra} : term (Bit * (Word n * Word n)) (Bit '
                   '* Word n) :=\n'
                   'match n with\n'
                   '| 0 => fullAdderBit\n'
                   '| S n => buildFullAdder fullAdder\n'
                   'end.\n'],
                  ['Coq/Simplicity/Word.v',
                   'declaration',
                   'adder',
                   'Definition adder {n : nat} {term : Core.Algebra} : term (Word n * Word n) (Bit * Word n) '
                   ':=\n'
                   'match n with\n'
                   '| 0 => adderBit\n'
                   '| S n => false &&& iden >>> fullAdder\n'
                   'end.\n'],
                  ['Coq/Simplicity/Word.v',
                   'declaration',
                   'bitwiseTri',
                   'Fixpoint bitwiseTri {X} {n : nat} {term : Core.Algebra} (op : term (X * (X * X)) X) :\n'
                   '  term (Vector X n * (Vector X n * Vector X n)) (Vector X n) :=\n'
                   'match n with\n'
                   '| 0 => op\n'
                   '| S n => buildBitwiseTri (bitwiseTri op)\n'
                   'end.\n'],
                  ['Coq/Simplicity/Word.v',
                   'declaration',
                   'shift_const_by',
                   'Definition shift_const_by {X n} {term : Core.Algebra} (t : term Unit X) (c : Z) \n'
                   ' : term (Vector X n) (Vector X n) :=\n'
                   'match c with\n'
                   '| Z0 => iden\n'
                   '| Zpos p => left_shift_const_by t p\n'
                   '| Zneg p => right_shift_const_by t p\n'
                   'end.\n'],
                  ['Coq/Simplicity/Word.v',
                   'declaration',
                   'shift_const',
                   'Definition shift_const {n} {term : Core.Algebra} : Z -> term (Vector Bit n) (Vector Bit '
                   'n) :=\n'
                   '  shift_const_by false.\n'],
                  ['Coq/Simplicity/Word.v',
                   'declaration',
                   'left_rotate1',
                   'Definition left_rotate1 {X n} {term : Core.Algebra} : term (Vector X n) (Vector X n) :=\n'
                   'iden &&& leftmost >>> full_left_shift1 >>> I H.\n'],
                  ['Coq/Simplicity/Word.v',
                   'declaration',
                   'right_rotate1',
                   'Definition right_rotate1 {X n} {term : Core.Algebra} : term (Vector X n) (Vector X n) '
                   ':=\n'
                   'rightmost &&& iden >>> full_right_shift1 >>> O H.\n'],
                  ['Coq/Simplicity/Word.v',
                   'declaration',
                   'rotate_const_list',
                   'Fixpoint rotate_const_list {X n} {term : Core.Algebra} (z : Z) \n'
                   ' : list (term (Vector X n) (Vector X n)) :=\n'
                   'match n with \n'
                   '| 0 => []\n'
                   '| (S n0) =>\n'
                   '  if Z.even z\n'
                   '  then eq_rect _ (fun x => list (term x x)) (rotate_const_list (Z.div z 2)%Z) _ (eq_sym '
                   'VectorPromote)\n'
                   '  else if Z.even (Z.div z 2)\n'
                   '  then left_rotate1 :: eq_rect _ (fun x => list (term x x)) (rotate_const_list (Z.div z '
                   '2)%Z) _ (eq_sym VectorPromote)\n'
                   '  else right_rotate1 :: eq_rect _ (fun x => list (term x x)) (rotate_const_list (Z.div '
                   '(z + 1) 2)%Z) _ (eq_sym VectorPromote)\n'
                   'end.\n'],
                  ['Coq/Simplicity/Word.v',
                   'declaration',
                   'foldr_comp',
                   'Fixpoint foldr_comp {X} {term : Core.Algebra} (l : list (term X X)) : term X X :=\n'
                   'match l with\n'
                   '| [] => iden\n'
                   '| i::[] => i\n'
                   '| i::l => i >>> foldr_comp l\n'
                   'end.\n'],
                  ['Coq/Simplicity/Word.v',
                   'declaration',
                   'rotate_const',
                   'Definition rotate_const {X n} {term : Core.Algebra} (z : Z) : term (Vector X n) (Vector '
                   'X n) :=\n'
                   'foldr_comp (rotate_const_list z).\n'],
                  ['Coq/Simplicity/Bit.v',
                   'declaration',
                   'false',
                   'Definition false {A} {term : Core.Algebra} : term A Bit := injl unit.'],
                  ['Coq/Simplicity/Bit.v',
                   'declaration',
                   'true',
                   'Definition true {A} {term : Core.Algebra} : term A Bit := injr unit.\n'],
                  ['Coq/Simplicity/Bit.v',
                   'declaration',
                   'cond',
                   'Definition cond {A B} {term : Core.Algebra} (thn els : term A B) : term (Bit * A) B :=\n'
                   '  case (drop els) (drop thn).\n'],
                  ['Coq/Simplicity/Bit.v',
                   'declaration',
                   'ch',
                   'Definition ch {A} {term : Core.Algebra} : term (Bit * (A * A)) A :=\n'
                   '  cond (O H) (I H).\n'],
                  ['Coq/Simplicity/Bit.v',
                   'declaration',
                   'not',
                   'Definition not {A} {term : Core.Algebra} (t : term A Bit) : term A Bit :=\n'
                   '  t &&& unit >>> cond false true.\n'],
                  ['Coq/Simplicity/Bit.v',
                   'declaration',
                   'xor3',
                   'Definition xor3 {term : Core.Algebra} : term (Bit * (Bit * Bit)) Bit :=\n'
                   '  cond (cond iden (not iden)) (cond (not iden) iden).\n'],
                  ['Coq/Simplicity/Bit.v',
                   'declaration',
                   'maj',
                   'Definition maj {term : Core.Algebra} : term (Bit * (Bit * Bit)) Bit :=\n'
                   '  cond (cond true iden) (cond iden false).\n'],
                  ['Coq/C/jet_buffer_empty_spec.v',
                   'declaration',
                   'buffer_type',
                   'Fixpoint buffer_type (X : Ty.Ty) (depth : nat) : Ty.Ty :=\n'
                   '  match depth with\n'
                   '  | Datatypes.O => Ty.Sum Ty.Unit X\n'
                   '  | Datatypes.S d => Ty.Prod (Ty.Sum Ty.Unit (Vector X (Datatypes.S d))) (buffer_type X '
                   'd)\n'
                   '  end.'],
                  ['Coq/C/jet_buffer_empty_spec.v',
                   'declaration',
                   'buffer_empty_spec',
                   'Fixpoint buffer_empty_spec (X : Ty.Ty) (depth : nat) (A : Ty.Ty) {term : '
                   'Alg.Core.Algebra} :\n'
                   '    term A (buffer_type X depth) :=\n'
                   '  match depth with\n'
                   '  | Datatypes.O => AC.injl AC.unit\n'
                   '  | Datatypes.S d => AC.pair (AC.injl AC.unit) (buffer_empty_spec X d A)\n'
                   '  end.'],
                  ['Coq/C/jet_sha256_ctx8_init_spec.v',
                   'declaration',
                   'sha256_ctx8_type',
                   'Definition sha256_ctx8_type := Ty.Prod (buffer_type (Word 3) 5) (Ty.Prod (Word 6) (Word '
                   '8)).'],
                  ['Coq/C/jet_sha256_ctx8_init_spec.v',
                   'declaration',
                   'sha256_ctx8_init_spec',
                   'Definition sha256_ctx8_init_spec {term : Alg.Core.Algebra} : term Ty.Unit '
                   'sha256_ctx8_type :=\n'
                   '  AC.pair (buffer_empty_spec (Word 3) 5 Ty.Unit) (AC.pair (@Word.zero 6 term) '
                   '(@sha256_iv_spec term)).\n'],
                  ['Coq/C/jet_sha256_iv_init.v',
                   'declaration',
                   'sha256_iv_constants',
                   'Definition sha256_iv_constants : list Z :=\n'
                   '  [1779033703; 3144134277; 1013904242; 2773480762;\n'
                   '   1359893119; 2600822924; 528734635; 1541459225].'],
                  ['Coq/C/jet_sha256_iv_init.v',
                   'declaration',
                   'sha256_iv_words',
                   'Definition sha256_iv_words := map uint32_init_value sha256_iv_constants.'],
                  ['Coq/C/jet_sha256_iv_init.v',
                   'declaration',
                   'sha256_iv_spec',
                   'Definition sha256_iv_spec {term : Alg.Core.Algebra} :\n'
                   '    @Alg.Core.domain term Ty.Unit (Word 8) :=\n'
                   '  Alg.scribe (@fromZ (WordToZ 8)\n'
                   '    0x6a09e667bb67ae853c6ef372a54ff53a510e527f9b05688c1f83d9ab5be0cd19).\n'],
                  ['Coq/C/jet_sha_ctx8_spec.v',
                   'declaration',
                   'buffer_snoc_spec',
                   'Fixpoint buffer_snoc_spec (X : Ty.Ty) (depth : nat) {term : Alg.Core.Algebra} :\n'
                   '    @Alg.Core.domain term (Ty.Prod (buffer_type X depth) X) (Ty.Sum (Vector X (S depth)) '
                   '(buffer_type X depth)) :=\n'
                   '  match depth with\n'
                   '  | O => AC.case (AC.injr (AC.injr (AC.drop AC.iden))) (AC.injl AC.iden)\n'
                   '  | S d =>\n'
                   '      AC.comp\n'
                   '        (AC.pair (AC.comp (AC.pair (AC.take (AC.drop AC.iden)) (AC.drop AC.iden)) '
                   '(buffer_snoc_spec X d))\n'
                   '                 (AC.take (AC.take AC.iden)))\n'
                   '        (AC.case\n'
                   '          (AC.comp (AC.pair (AC.drop AC.iden) (AC.take AC.iden))\n'
                   '            (AC.case (AC.injr (AC.pair (AC.injr (AC.drop AC.iden)) (buffer_empty_spec X '
                   'd _)))\n'
                   '                     (AC.injl AC.iden)))\n'
                   '          (AC.injr (AC.pair (AC.drop AC.iden) (AC.take AC.iden))))\n'
                   '  end.\n'],
                  ['Coq/C/jet_sha_ctx8_spec.v',
                   'declaration',
                   'ctx8_buf',
                   'Definition ctx8_buf := buffer_type (Word 3) 5.'],
                  ['Coq/C/jet_sha_ctx8_spec.v',
                   'declaration',
                   'ctx8_tail',
                   'Definition ctx8_tail := Ty.Prod (Word 6) (Word 8).\n\n '],
                  ['Coq/C/jet_sha_ctx8_spec.v',
                   'declaration',
                   'ctx8_add1_snoc',
                   'Definition ctx8_add1_snoc {term : Alg.Core.Algebra} :\n'
                   '    @Alg.Core.domain term (Ty.Prod sha256_ctx8_type (Word 3)) (Ty.Prod (Ty.Sum (Word 9) '
                   'ctx8_buf) ctx8_tail) :=\n'
                   '  AC.pair\n'
                   '    (AC.comp (AC.pair (AC.take (AC.take AC.iden)) (AC.drop AC.iden)) (buffer_snoc_spec '
                   '(Word 3) 5))\n'
                   '    (AC.take (AC.drop AC.iden)).\n'
                   '\n'
                   ' \n'],
                  ['Coq/C/jet_sha_ctx8_spec.v',
                   'declaration',
                   'ctx8_add1_full',
                   'Definition ctx8_add1_full {term : Alg.Assertion.Algebra} :\n'
                   '    @Alg.Assertion.domain term (Ty.Prod (Word 9) ctx8_tail) sha256_ctx8_type :=\n'
                   '  AC.pair (AC.comp AC.unit (buffer_empty_spec (Word 3) 5 Ty.Unit))\n'
                   '    (AC.pair\n'
                   '      (AC.drop (AC.comp (AC.take (@increment_word_spec (Alg.Assertion.toCore term) 6))\n'
                   '        (@Alg.Assertion.Combinators.assertl Ty.Unit Ty.Unit (Word 6) (Word 6) term\n'
                   '          (@AC.drop Ty.Unit (Word 6) (Word 6) (Alg.Assertion.toCore term) (@AC.iden '
                   '(Word 6) (Alg.Assertion.toCore term)))\n'
                   '          assertion_cmr_fail0)))\n'
                   '      (AC.comp (AC.pair (AC.drop (AC.drop AC.iden)) (AC.take AC.iden)) '
                   'Simplicity.SHA256.hashBlock)).\n'],
                  ['Coq/C/jet_sha_ctx8_spec.v',
                   'declaration',
                   'ctx8_add1_spec',
                   'Definition ctx8_add1_spec {term : Alg.Assertion.Algebra} :\n'
                   '    @Alg.Assertion.domain term (Ty.Prod sha256_ctx8_type (Word 3)) sha256_ctx8_type :=\n'
                   '  AC.comp (@ctx8_add1_snoc (Alg.Assertion.toCore term))\n'
                   '    (AC.comp (@AC.case _ _ _ _ (Alg.Assertion.toCore term) (@ctx8_add1_full term) '
                   'AC.iden)\n'
                   '      (AC.comp (@AC.pair _ _ _ (Alg.Assertion.toCore term) (@sha256_count_assertion_spec '
                   'term) AC.iden)\n'
                   '        (AC.drop AC.iden))).\n'],
                  ['Coq/C/jet_sha_ctx8_spec.v',
                   'declaration',
                   'ctx8_limit',
                   'Definition ctx8_limit : Z := 36028797018963968.\n'],
                  ['Coq/C/jet_sha_ctx8_spec.v',
                   'declaration',
                   'ctx8_addn_spec',
                   'Fixpoint ctx8_addn_spec (n : nat) {term : Alg.Assertion.Algebra} :\n'
                   '    @Alg.Assertion.domain term (Ty.Prod sha256_ctx8_type (Vector (Word 3) n)) '
                   'sha256_ctx8_type :=\n'
                   '  match n with\n'
                   '  | O => @ctx8_add1_spec term\n'
                   '  | S n =>\n'
                   '      @AC.comp _ _ _ (Alg.Assertion.toCore term)\n'
                   '        (@AC.pair _ _ _ (Alg.Assertion.toCore term)\n'
                   '          (@AC.comp _ _ _ (Alg.Assertion.toCore term)\n'
                   '            (AC.pair (AC.take AC.iden) (AC.drop (AC.take AC.iden))) (@ctx8_addn_spec n '
                   'term))\n'
                   '          (AC.drop (AC.drop AC.iden)))\n'
                   '        (@ctx8_addn_spec n term)\n'
                   '  end.\n'],
                  ['Coq/C/jet_sha_add_buffer_spec.v',
                   'declaration',
                   'ctx8_add_buffer_spec',
                   'Fixpoint ctx8_add_buffer_spec (d : nat) {term : Alg.Assertion.Algebra} :\n'
                   '    @Alg.Assertion.domain term (Ty.Prod sha256_ctx8_type (buffer_type (Word 3) d)) '
                   'sha256_ctx8_type :=\n'
                   '  match d with\n'
                   '  | O =>\n'
                   '      @AC.comp _ _ _ (Alg.Assertion.toCore term) (AC.pair (AC.drop AC.iden) (AC.take '
                   'AC.iden))\n'
                   '        (@AC.case _ _ _ _ (Alg.Assertion.toCore term)\n'
                   '          (@AC.drop _ _ _ (Alg.Assertion.toCore term)\n'
                   '            (@AC.comp _ _ _ (Alg.Assertion.toCore term)\n'
                   '              (@AC.pair _ _ _ (Alg.Assertion.toCore term) AC.iden '
                   '(@sha256_count_assertion_spec term))\n'
                   '              (AC.take AC.iden)))\n'
                   '          (@AC.comp _ _ _ (Alg.Assertion.toCore term) (AC.pair (AC.drop AC.iden) '
                   '(AC.take AC.iden))\n'
                   '            (@ctx8_add1_spec term)))\n'
                   "  | S d' =>\n"
                   '      @AC.comp _ _ _ (Alg.Assertion.toCore term)\n'
                   '        (@AC.pair _ _ _ (Alg.Assertion.toCore term)\n'
                   '          (@AC.comp _ _ _ (Alg.Assertion.toCore term)\n'
                   '            (AC.pair (AC.drop (AC.take AC.iden)) (AC.take AC.iden))\n'
                   '            (@AC.case _ _ _ _ (Alg.Assertion.toCore term) (AC.drop AC.iden)\n'
                   '              (@AC.comp _ _ _ (Alg.Assertion.toCore term) (AC.pair (AC.drop AC.iden) '
                   '(AC.take AC.iden))\n'
                   "                (@ctx8_addn_spec (S d') term))))\n"
                   '          (AC.drop (AC.drop AC.iden)))\n'
                   "        (@ctx8_add_buffer_spec d' term)\n"
                   '  end.\n'],
                  ['Coq/C/jet_sha_finalize_spec.v',
                   'declaration',
                   'buffer_pad_spec',
                   'Fixpoint buffer_pad_spec (d : nat) {term : Alg.Core.Algebra} :\n'
                   '    @Alg.Core.domain term (buffer_type (Word 3) d) (Vector (Word 3) (S d)) :=\n'
                   '  match d with\n'
                   '  | O => AC.copair (@Word.zero 4 term) (AC.pair AC.iden (AC.comp AC.unit (@Word.zero 3 '
                   'term)))\n'
                   "  | S d' =>\n"
                   "      AC.comp (AC.pair (AC.take AC.iden) (AC.drop (buffer_pad_spec d')))\n"
                   '        (AC.case\n'
                   "          (AC.pair (AC.drop AC.iden) (AC.take (@fill Ty.Unit (Word 3) (S d') term "
                   '(@Word.zero 3 term))))\n'
                   '          AC.iden)\n'
                   '  end.\n'],
                  ['Coq/C/jet_sha_finalize_spec.v',
                   'declaration',
                   'flag_spec',
                   'Definition flag_spec {X : Ty.Ty} {term : Alg.Core.Algebra} :\n'
                   '    @Alg.Core.domain term (Ty.Sum Ty.Unit X) Bit :=\n'
                   '  AC.copair Bit.false Bit.true.\n'],
                  ['Coq/C/jet_sha_finalize_spec.v',
                   'declaration',
                   'buffer63_size_spec',
                   'Definition buffer63_size_spec {term : Alg.Core.Algebra} :\n'
                   '    @Alg.Core.domain term (buffer_type (Word 3) 5) (Word 3) :=\n'
                   '  AC.pair\n'
                   '    (AC.pair (AC.pair Bit.false Bit.false)\n'
                   '             (AC.pair (AC.take flag_spec) (AC.drop (AC.take flag_spec))))\n'
                   '    (AC.drop (AC.drop\n'
                   '      (AC.pair (AC.pair (AC.take flag_spec) (AC.drop (AC.take flag_spec)))\n'
                   '               (AC.drop (AC.drop (AC.pair (AC.take flag_spec) (AC.drop '
                   'flag_spec))))))).\n'],
                  ['Coq/C/jet_sha_finalize_spec.v',
                   'declaration',
                   'ctx8_bitlen_spec',
                   'Definition ctx8_bitlen_spec {term : Alg.Core.Algebra} :\n'
                   '    @Alg.Core.domain term sha256_ctx8_type (Word 6) :=\n'
                   '  AC.comp\n'
                   '    (AC.pair (AC.comp (AC.take buffer63_size_spec) (@left_pad_low_spec term 3 3))\n'
                   '             (AC.drop (AC.take (@Word.shift_const 6 term 6))))\n'
                   '    (AC.comp (AC.comp (@Word.adder 6 term) (AC.drop AC.iden)) (@Word.shift_const 6 term '
                   '3)).\n'],
                  ['Coq/C/jet_sha_finalize_spec.v',
                   'declaration',
                   'pad_word64',
                   'Definition pad_word64 : Ty.tySem (Word 6) := @fromZ (WordToZ 6) 9223372036854775808.\n'
                   '\n'
                   ' '],
                  ['Coq/C/jet_sha_finalize_spec.v',
                   'declaration',
                   'ctx8_clear_count_spec',
                   'Definition ctx8_clear_count_spec {term : Alg.Assertion.Algebra} :\n'
                   '    @Alg.Assertion.domain term sha256_ctx8_type sha256_ctx8_type :=\n'
                   '  @AC.pair _ _ _ (Alg.Assertion.toCore term) (AC.take AC.iden)\n'
                   '    (@AC.pair _ _ _ (Alg.Assertion.toCore term)\n'
                   '      (@AC.comp _ _ _ (Alg.Assertion.toCore term) (@sha256_count_assertion_spec term)\n'
                   '        (@Word.zero 6 (Alg.Assertion.toCore term)))\n'
                   '      (AC.drop (AC.drop AC.iden))).\n'
                   '\n'
                   ' '],
                  ['Coq/C/jet_sha_finalize_spec.v',
                   'declaration',
                   'ctx8_finalize_pad_spec',
                   'Definition ctx8_finalize_pad_spec {term : Alg.Assertion.Algebra} :\n'
                   '    @Alg.Assertion.domain term sha256_ctx8_type (Ty.Prod (Word 9) (Word 8)) :=\n'
                   '  @AC.comp _ _ _ (Alg.Assertion.toCore term)\n'
                   '    (@AC.pair _ _ (Word 6) (Alg.Assertion.toCore term) (@ctx8_clear_count_spec term)\n'
                   '      (AC.comp AC.unit (Alg.scribe pad_word64)))\n'
                   '    (@AC.comp _ _ _ (Alg.Assertion.toCore term) (@ctx8_addn_spec 3 term)\n'
                   '      (AC.pair (AC.take (@buffer_pad_spec 5 (Alg.Assertion.toCore term))) (AC.drop '
                   '(AC.drop AC.iden)))).\n'
                   '\n'
                   ' '],
                  ['Coq/C/jet_sha_finalize_spec.v',
                   'declaration',
                   'ctx8_finalize_block_spec',
                   'Definition ctx8_finalize_block_spec {term : Alg.Core.Algebra} :\n'
                   '    @Alg.Core.domain term (Ty.Prod (Ty.Prod (Word 9) (Word 8)) (Word 6)) (Ty.Prod (Word '
                   '8) (Word 9)) :=\n'
                   '  AC.pair (AC.take (AC.drop AC.iden))\n'
                   '    (AC.pair (AC.take (AC.take (AC.take AC.iden)))\n'
                   '      (AC.pair (AC.take (AC.take (AC.drop (AC.take AC.iden))))\n'
                   '        (AC.pair (AC.take (AC.take (AC.drop (AC.drop (AC.take AC.iden))))) (AC.drop '
                   'AC.iden)))).\n'],
                  ['Coq/C/jet_sha_finalize_spec.v',
                   'declaration',
                   'ctx8_finalize_spec',
                   'Definition ctx8_finalize_spec {term : Alg.Assertion.Algebra} :\n'
                   '    @Alg.Assertion.domain term sha256_ctx8_type (Word 8) :=\n'
                   '  @AC.comp _ _ _ (Alg.Assertion.toCore term)\n'
                   '    (@AC.pair _ _ _ (Alg.Assertion.toCore term) (@ctx8_finalize_pad_spec term)\n'
                   '      (@ctx8_bitlen_spec (Alg.Assertion.toCore term)))\n'
                   '    (AC.comp (@ctx8_finalize_block_spec (Alg.Assertion.toCore term)) '
                   'Simplicity.SHA256.hashBlock).\n'],
                  ['Coq/C/jet_sha256_count_assertion.v',
                   'declaration',
                   'sha256_count_limit',
                   'Definition sha256_count_limit : Ty.tySem (Word 6) := @fromZ (WordToZ 6) '
                   '36028797018963968.'],
                  ['Coq/C/jet_sha256_count_assertion.v',
                   'declaration',
                   'sha256_count_check_spec',
                   'Definition sha256_count_check_spec {term : Alg.Core.Algebra} :\n'
                   '    @Alg.Core.domain term sha256_ctx8_type Bit :=\n'
                   '  AC.comp (AC.pair (AC.drop (AC.take AC.iden))\n'
                   '    (AC.comp AC.unit (Alg.scribe sha256_count_limit))) (@lt_word_spec term 6).'],
                  ['Coq/C/jet_sha256_count_assertion.v',
                   'declaration',
                   'sha256_count_assertion_spec',
                   'Definition sha256_count_assertion_spec {term : Alg.Assertion.Algebra} :\n'
                   '    @Alg.Assertion.domain term sha256_ctx8_type Ty.Unit :=\n'
                   '  AC.comp (AC.pair (@sha256_count_check_spec term) AC.unit)\n'
                   '    (Alg.Assertion.Combinators.assertr assertion_cmr_fail0 (AC.take AC.iden)).\n'],
                  ['Coq/C/jet_assertion_spec.v',
                   'declaration',
                   'assertion_hash0',
                   'Definition assertion_hash0 : Simplicity.Digest.hash256 :=\n'
                   '  Simplicity.Digest.Hash256\n'
                   '    [Int.zero; Int.zero; Int.zero; Int.zero; Int.zero; Int.zero; Int.zero; Int.zero]\n'
                   '    eq_refl.'],
                  ['Coq/C/jet_assertion_spec.v',
                   'declaration',
                   'assertion_cmr_fail0',
                   'Definition assertion_cmr_fail0 : Simplicity.Digest.hash256 :=\n'
                   '  @Alg.Assertion.Combinators.fail Ty.Unit Ty.Unit\n'
                   '    Simplicity.MerkleRoot.CommitmentRoot_Assertion_alg (assertion_hash0, '
                   'assertion_hash0).\n'],
                  ['Coq/C/jet_increment_spec.v',
                   'declaration',
                   'full_increment_word_spec',
                   'Definition full_increment_word_spec {term : Alg.Core.Algebra} (n : nat) :\n'
                   '    @Alg.Core.domain term (Ty.Prod Bit (Word n)) (Ty.Prod Bit (Word n)) :=\n'
                   '  @Alg.Core.Combinators.comp (Ty.Prod Bit (Word n))\n'
                   '    (Ty.Prod Bit (Ty.Prod (Word n) (Word n))) (Ty.Prod Bit (Word n)) term\n'
                   '    (@Alg.Core.Combinators.pair (Ty.Prod Bit (Word n)) Bit\n'
                   '      (Ty.Prod (Word n) (Word n)) term\n'
                   '      (@Alg.Core.Combinators.take Bit (Word n) Bit term\n'
                   '        (@Alg.Core.Combinators.iden Bit term))\n'
                   '      (@Alg.Core.Combinators.pair (Ty.Prod Bit (Word n)) (Word n) (Word n) term\n'
                   '        (@Alg.Core.Combinators.drop Bit (Word n) (Word n) term\n'
                   '          (@Alg.Core.Combinators.iden (Word n) term))\n'
                   '        (@Alg.Core.Combinators.comp (Ty.Prod Bit (Word n)) Ty.Unit (Word n) term\n'
                   '          (@Alg.Core.Combinators.unit (Ty.Prod Bit (Word n)) term)\n'
                   '          (@Word.zero n term))))\n'
                   '    (@Word.fullAdder n term).\n'],
                  ['Coq/C/jet_increment_spec.v',
                   'declaration',
                   'increment_word_spec',
                   'Definition increment_word_spec {term : Alg.Core.Algebra} (n : nat) :\n'
                   '    @Alg.Core.domain term (Word n) (Ty.Prod Bit (Word n)) :=\n'
                   '  @Alg.Core.Combinators.comp (Word n) (Ty.Prod Bit (Word n))\n'
                   '    (Ty.Prod Bit (Word n)) term\n'
                   '    (@Alg.Core.Combinators.pair (Word n) Bit (Word n) term\n'
                   '      (@Bit.true (Word n) term) (@Alg.Core.Combinators.iden (Word n) term))\n'
                   '    (@full_increment_word_spec term n).\n'],
                  ['Coq/C/jet_bitcoin_ctx_hash_spec.v',
                   'declaration',
                   'outpoint_hash_spec',
                   'Definition outpoint_hash_spec {term : Alg.Assertion.Algebra} :\n'
                   '    @Alg.Assertion.domain term (Ty.Prod sha256_ctx8_type (Ty.Prod (Word 8) (Word 5))) '
                   'sha256_ctx8_type :=\n'
                   '  @AC.comp _ _ _ (Alg.Assertion.toCore term)\n'
                   '    (@AC.pair _ _ _ (Alg.Assertion.toCore term)\n'
                   '      (@AC.comp _ _ _ (Alg.Assertion.toCore term)\n'
                   '        (AC.pair (AC.take AC.iden) (AC.drop (AC.take AC.iden))) (@ctx8_addn_spec 5 '
                   'term))\n'
                   '      (AC.drop (AC.drop AC.iden)))\n'
                   '    (@ctx8_addn_spec 2 term).\n'],
                  ['Coq/C/jet_bitcoin_ctx_hash_spec.v',
                   'declaration',
                   'byte_one',
                   'Definition byte_one : Ty.tySem (Word 3) := @fromZ (WordToZ 3) 1.\n'],
                  ['Coq/C/jet_bitcoin_ctx_hash_spec.v',
                   'declaration',
                   'annex_hash_spec',
                   'Definition annex_hash_spec {term : Alg.Assertion.Algebra} :\n'
                   '    @Alg.Assertion.domain term (Ty.Prod sha256_ctx8_type (Ty.Sum Ty.Unit (Word 8))) '
                   'sha256_ctx8_type :=\n'
                   '  @AC.comp _ _ _ (Alg.Assertion.toCore term) (AC.pair (AC.drop AC.iden) (AC.take '
                   'AC.iden))\n'
                   '    (@AC.case _ _ _ _ (Alg.Assertion.toCore term)\n'
                   '      (@AC.comp _ _ _ (Alg.Assertion.toCore term)\n'
                   '        (AC.pair (AC.drop AC.iden) (AC.take (@Word.zero 3 (Alg.Assertion.toCore '
                   'term))))\n'
                   '        (@ctx8_add1_spec term))\n'
                   '      (@AC.comp _ _ _ (Alg.Assertion.toCore term)\n'
                   '        (@AC.pair _ _ _ (Alg.Assertion.toCore term)\n'
                   '          (@AC.comp _ _ _ (Alg.Assertion.toCore term)\n'
                   '            (AC.pair (AC.drop AC.iden) (AC.comp AC.unit (Alg.scribe byte_one)))\n'
                   '            (@ctx8_add1_spec term))\n'
                   '          (AC.take AC.iden))\n'
                   '        (@ctx8_addn_spec 5 term))).\n'],
                  ['Coq/C/jet_sha_tapdata_spec.v',
                   'declaration',
                   'tapdata_prefix',
                   'Definition tapdata_prefix : Ty.tySem (Word 8) :=\n'
                   '  @fromZ (WordToZ 8) '
                   '40667712476135943074815926098399800589563142586032845238766438666671440893918.\n'
                   '\n'
                   ' '],
                  ['Coq/C/jet_sha_tapdata_spec.v',
                   'declaration',
                   'one64_spec',
                   'Definition one64_spec {term : Alg.Core.Algebra} : @Alg.Core.domain term Ty.Unit (Word 6) '
                   ':=\n'
                   '  AC.comp Bit.true (left_pad_low_1_n 6).\n'],
                  ['Coq/C/jet_sha_tapdata_spec.v',
                   'declaration',
                   'tapdata_init_spec',
                   'Definition tapdata_init_spec {term : Alg.Core.Algebra} :\n'
                   '    @Alg.Core.domain term Ty.Unit sha256_ctx8_type :=\n'
                   '  AC.pair (buffer_empty_spec (Word 3) 5 Ty.Unit) (AC.pair one64_spec (Alg.scribe '
                   'tapdata_prefix)).\n'],
                  ['Coq/C/jet_sha_tapdata_spec.v',
                   'declaration',
                   'iv_word',
                   'Definition iv_word : Ty.tySem (Word 8) :=\n'
                   '  @fromZ (WordToZ 8) '
                   '0x6a09e667bb67ae853c6ef372a54ff53a510e527f9b05688c1f83d9ab5be0cd19.'],
                  ['Coq/C/jet_sha_tapdata_spec.v',
                   'declaration',
                   'tag_word',
                   'Definition tag_word : Ty.tySem (Word 8) :=\n'
                   '  @fromZ (WordToZ 8) '
                   '112633728163065979925619053251602456653929709242813588906169298812374638486850.'],
                  ['Coq/C/jet_sha_tapdata_spec.v',
                   'declaration',
                   'tag_block',
                   'Definition tag_block : Ty.tySem (Word 9) :=\n'
                   '  @fromZ (WordToZ 9) '
                   '4419371627814514849444849851556384968781224120886322008369998198262556832457228456145577973000179191792448113899619522729437796388078023106436640385531960.\n'],
                  ['Coq/C/jet_sha_tapdata_spec.v',
                   'declaration',
                   'tag_bytes',
                   'Definition tag_bytes : list int :=\n  map Int.repr [84; 97; 112; 68; 97; 116; 97].\n'],
                  ['Coq/C/jet_bitcoin_tapleaf_hash_spec.v',
                   'declaration',
                   'tapleaf_prefix',
                   'Definition tapleaf_prefix : Ty.tySem (Word 8) :=\n'
                   '  @fromZ (WordToZ 8) '
                   '70958157933520607839019537422246167060091032002336751475331932121621309354185.'],
                  ['Coq/C/jet_bitcoin_tapleaf_hash_spec.v',
                   'declaration',
                   'tapleaf_tag_word',
                   'Definition tapleaf_tag_word : Ty.tySem (Word 8) :=\n'
                   '  @fromZ (WordToZ 8) '
                   '79116870754516498155377025264173316429806398436674791508357063697857940875758.'],
                  ['Coq/C/jet_bitcoin_tapleaf_hash_spec.v',
                   'declaration',
                   'tapleaf_tag_block',
                   'Definition tapleaf_tag_block : Ty.tySem (Word 9) :=\n'
                   '  @fromZ (WordToZ 9) '
                   '4419371652836376455474968878630918397760145670010128363765783181683530450169627206189720363646590656808003891873351972755786637110606967735627562008707128.'],
                  ['Coq/C/jet_bitcoin_tapleaf_hash_spec.v',
                   'declaration',
                   'tapleaf_tag_bytes',
                   'Definition tapleaf_tag_bytes : list int := map Int.repr [84; 97; 112; 76; 101; 97; '
                   '102].\n'],
                  ['Coq/C/jet_bitcoin_tapleaf_hash_spec.v',
                   'declaration',
                   'byte32',
                   'Definition byte32 : Ty.tySem (Word 3) := @fromZ (WordToZ 3) 32.\n'],
                  ['Coq/C/jet_bitcoin_build_tapleaf_spec.v',
                   'declaration',
                   'tl_version',
                   'Definition tl_version : Ty.tySem (Word 3) := @fromZ (WordToZ 3) 190.'],
                  ['Coq/C/jet_bitcoin_build_tapleaf_spec.v',
                   'declaration',
                   'tl_w8000',
                   'Definition tl_w8000 : Ty.tySem (Word 4) := @fromZ (WordToZ 4) 32768.'],
                  ['Coq/C/jet_bitcoin_build_tapleaf_spec.v',
                   'declaration',
                   'tl_len',
                   'Definition tl_len : Ty.tySem (Word 7) := @fromZ (WordToZ 7) 784.\n'],
                  ['Coq/C/jet_bitcoin_build_tapleaf_spec.v',
                   'declaration',
                   'build_tapleaf_block',
                   'Definition build_tapleaf_block {term : Alg.Core.Algebra} : @Alg.Core.domain term (Word '
                   '8) (Word 9) :=\n'
                   '  AC.comp\n'
                   '    (AC.pair (AC.comp AC.unit (AC.pair (Alg.scribe tl_version) (Alg.scribe byte32))) '
                   'AC.iden)\n'
                   '    (AC.comp (@Word.full_right_shift1 (Word 4) 4 term)\n'
                   '      (AC.pair (AC.take AC.iden)\n'
                   '        (AC.pair\n'
                   '          (AC.pair\n'
                   '            (AC.pair (AC.pair (AC.drop AC.iden) (AC.comp AC.unit (Alg.scribe '
                   'tl_w8000)))\n'
                   '              (AC.comp AC.unit (@Word.zero 5 term)))\n'
                   '            (AC.comp AC.unit (@Word.zero 6 term)))\n'
                   '          (AC.comp AC.unit (Alg.scribe tl_len))))).\n'],
                  ['Coq/C/jet_bitcoin_build_tapleaf_spec.v',
                   'declaration',
                   'build_tapleaf_spec',
                   'Definition build_tapleaf_spec {term : Alg.Core.Algebra} : @Alg.Core.domain term (Word 8) '
                   '(Word 8) :=\n'
                   '  AC.comp (AC.pair (AC.comp AC.unit (Alg.scribe tapleaf_prefix)) (@build_tapleaf_block '
                   'term))\n'
                   '    (@Simplicity.SHA256.hashBlock term).\n'],
                  ['Coq/C/jet_bitcoin_build_tapbranch_spec.v',
                   'declaration',
                   'tapbranch_prefix',
                   'Definition tapbranch_prefix : Ty.tySem (Word 8) :=\n'
                   '  @fromZ (WordToZ 8) '
                   '16128481659354054051886650070918308588707920384911815168968115687213851879122.'],
                  ['Coq/C/jet_bitcoin_build_tapbranch_spec.v',
                   'declaration',
                   'tapbranch_tag_word',
                   'Definition tapbranch_tag_word : Ty.tySem (Word 8) :=\n'
                   '  @fromZ (WordToZ 8) '
                   '11423784003423245473257913154601382734653671235488771667104991518695318003733.'],
                  ['Coq/C/jet_bitcoin_build_tapbranch_spec.v',
                   'declaration',
                   'tapbranch_tag_block',
                   'Definition tapbranch_tag_block : Ty.tySem (Word 9) :=\n'
                   '  @fromZ (WordToZ 9) '
                   '4419371621777418713669862736773585009732451909885880897487510725603506506676440551277137483196335502719270104272573258040306099979007799678344122037436488.'],
                  ['Coq/C/jet_bitcoin_build_tapbranch_spec.v',
                   'declaration',
                   'tapbranch_tag_bytes',
                   'Definition tapbranch_tag_bytes : list int := map Int.repr [84; 97; 112; 66; 114; 97; '
                   '110; 99; 104].\n'],
                  ['Coq/C/jet_bitcoin_build_tapbranch_spec.v',
                   'declaration',
                   'tb_padblock',
                   'Definition tb_padblock : Ty.tySem (Word 9) := @fromZ (WordToZ 9) (2 ^ 511 + 1024).\n'],
                  ['Coq/C/jet_bitcoin_build_tapbranch_spec.v',
                   'declaration',
                   'build_tapbranch_spec',
                   'Definition build_tapbranch_spec {term : Alg.Core.Algebra} : @Alg.Core.domain term (Word '
                   '9) (Word 8) :=\n'
                   '  AC.comp\n'
                   '    (AC.pair\n'
                   '      (AC.comp\n'
                   '        (AC.pair (AC.comp AC.unit (Alg.scribe tapbranch_prefix))\n'
                   '          (AC.comp (AC.pair (@lt_word_spec term 8) AC.iden)\n'
                   '            (Bit.cond AC.iden (AC.pair (AC.drop AC.iden) (AC.take AC.iden)))))\n'
                   '        (@Simplicity.SHA256.hashBlock term))\n'
                   '      (AC.comp AC.unit (Alg.scribe tb_padblock)))\n'
                   '    (@Simplicity.SHA256.hashBlock term).\n'],
                  ['Coq/C/jet_sha_linkage.v',
                   'declaration',
                   'sha_ge',
                   'Definition sha_ge : Clight.genv := Clight.globalenv jets_sha.prog.'],
                  ['Coq/C/jet_sha_startup_state.v',
                   'declaration',
                   'sha_tag_extents',
                   'Definition sha_tag_extents (m : mem) : Prop :=\n'
                   '  (forall ofs p, Mem.perm m (sha_symbol_block _tagName) ofs Max p -> 0 <= ofs < 8) /\\\n'
                   '  (forall ofs p, Mem.perm m (sha_symbol_block _tagName__1) ofs Max p -> 0 <= ofs < 8) '
                   '/\\\n'
                   '  (forall ofs p, Mem.perm m (sha_symbol_block _tagName__2) ofs Max p -> 0 <= ofs < '
                   '10).\n'],
                  ['Coq/C/jet_sha_startup_state.v',
                   'declaration',
                   'sha_tags_state',
                   'Definition sha_tags_state (m : mem) : Prop :=\n'
                   '  sha_tag_ok m /\\ sha_tapleaf_tag_ok m /\\ sha_tapbranch_tag_ok m /\\ sha_tag_extents '
                   'm.\n'],
                  ['Coq/C/jet_sha_startup_state.v',
                   'declaration',
                   'sha_startup_state',
                   'Definition sha_startup_state (m : mem) : Prop :=\n'
                   '  sha_persistent_global_state m /\\ sha_tags_state m.\n'],
                  ['Coq/C/jet_sha_startup_state.v',
                   'declaration',
                   'sha_startup_total_spec',
                   'Definition sha_startup_total_spec (f : function) (A B : Ty) (spec : A -> B) : Prop :=\n'
                   '  forall env m bd dbase bs sbase bi bw edge outedge cursor read_cursor (a : A),\n'
                   '    sha_startup_state m ->\n'
                   '    frame_base_valid sbase -> (8 | sbase) ->\n'
                   '    frame_fields_at m bs sbase bi edge read_cursor ->\n'
                   '    0 <= read_cursor -> read_cursor + Z.of_nat (bitSize A) <= Int64.max_unsigned ->\n'
                   '    frame_input_cells_at m bi edge read_cursor (encode a) ->\n'
                   '    write_frame_at m bd dbase bw outedge cursor (Z.of_nat (bitSize B)) ->\n'
                   '    exists mf,\n'
                   '      Clight2.eval_funcall sha_ge m (Internal f)\n'
                   '        [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]\n'
                   '        E0 mf (Vint Int.one) /\\\n'
                   '      frame_output_cells_at mf bw outedge cursor (encode (spec a)) /\\\n'
                   '      write_prefix_at m mf bw outedge cursor /\\\n'
                   '      frame_fields_at mf bd dbase bw outedge (cursor - Z.of_nat (bitSize B)) /\\\n'
                   '      (forall chunk b ofs, Mem.valid_block m b ->\n'
                   '        (b <> bd \\/ ofs + size_chunk chunk <= dbase + 8 \\/ dbase + 16 <= ofs) ->\n'
                   '        (b <> bw \\/\n'
                   '          ofs + size_chunk chunk <= outedge + 8 * ((cursor - Z.of_nat (bitSize B)) / 64) '
                   '\\/\n'
                   '          write_word_address outedge cursor + 8 <= ofs) ->\n'
                   '        Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\\\n'
                   '      sha_startup_state mf.\n'],
                  ['Coq/C/jet_sha_startup_state.v',
                   'declaration',
                   'sha_startup_partial_spec',
                   'Definition sha_startup_partial_spec (f : function) (A B : Ty) (spec : A -> option B) : '
                   'Prop :=\n'
                   '  forall env m bd dbase bs sbase bi bw edge outedge cursor read_cursor (a : A),\n'
                   '    sha_startup_state m ->\n'
                   '    frame_base_valid sbase -> (8 | sbase) ->\n'
                   '    frame_fields_at m bs sbase bi edge read_cursor ->\n'
                   '    0 <= read_cursor -> read_cursor + Z.of_nat (bitSize A) <= Int64.max_unsigned ->\n'
                   '    frame_input_cells_at m bi edge read_cursor (encode a) ->\n'
                   '    write_frame_at m bd dbase bw outedge cursor (Z.of_nat (bitSize B)) ->\n'
                   '    exists mf,\n'
                   '      Clight2.eval_funcall sha_ge m (Internal f)\n'
                   '        [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]\n'
                   '        E0 mf (jet_partial_return (spec a)) /\\\n'
                   '      (match spec a with\n'
                   '       | Some b => frame_output_cells_at mf bw outedge cursor (encode b) /\\\n'
                   '           write_prefix_at m mf bw outedge cursor /\\\n'
                   '           frame_fields_at mf bd dbase bw outedge (cursor - Z.of_nat (bitSize B))\n'
                   '       | None => True\n'
                   '       end) /\\\n'
                   '      (forall chunk b ofs, Mem.valid_block m b ->\n'
                   '        (b <> bd \\/ ofs + size_chunk chunk <= dbase + 8 \\/ dbase + 16 <= ofs) ->\n'
                   '        (b <> bw \\/\n'
                   '          ofs + size_chunk chunk <= outedge + 8 * ((cursor - Z.of_nat (bitSize B)) / 64) '
                   '\\/\n'
                   '          write_word_address outedge cursor + 8 <= ofs) ->\n'
                   '        Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\\\n'
                   '      sha_startup_state mf.\n'],
                  ['Coq/C/jet_sha_startup_globals.v',
                   'declaration',
                   'sha_persistent_global_state',
                   'Definition sha_persistent_global_state (m : mem) : Prop :=\n'
                   '  sha_globals_ok m /\\\n'
                   '  (forall ofs, ~ Mem.perm m (sha_symbol_block _sha256_max_counter) ofs Max Writable) '
                   '/\\\n'
                   '  (forall ofs p, Mem.perm m (sha_symbol_block _simplicity_sha256_compression) ofs Max p '
                   '->\n'
                   '    0 <= ofs < 8).\n'],
                  ['Coq/C/jet_sha_add_n_exec.v',
                   'declaration',
                   'sha_globals_ok',
                   'Definition sha_globals_ok (m : mem) : Prop :=\n'
                   '  sha_dispatch_ok m /\\\n'
                   '  Mem.load Mint64 m (sha_symbol_block _sha256_max_counter) 0 = Some (Vlong '
                   'sha_max_counter).\n'],
                  ['Coq/C/jet_sha_block_local.v',
                   'declaration',
                   'sha_dispatch_ok',
                   'Definition sha_dispatch_ok (m : mem) : Prop :=\n'
                   '  Mem.load Mptr m (sha_symbol_block _simplicity_sha256_compression) 0 =\n'
                   '    Some (Vptr (sha_symbol_block _sha256_compression_portable) Ptrofs.zero).\n'
                   '\n'
                   ' '],
                  ['Coq/C/jet_sha_tapdata_jet.v',
                   'declaration',
                   'sha_tag_ok',
                   'Definition sha_tag_ok (m : mem) : Prop :=\n'
                   '  forall i, (i < 7)%nat ->\n'
                   '    Mem.load Mint8unsigned m (sha_symbol_block _tagName) (Z.of_nat i) = Some (Vint (nth '
                   'i tag_bytes Int.zero)).\n'],
                  ['Coq/C/jet_bitcoin_make_tapleaf_exec.v',
                   'declaration',
                   'sha_tapleaf_tag_ok',
                   'Definition sha_tapleaf_tag_ok (m : mem) : Prop :=\n'
                   '  forall i, (i < 7)%nat ->\n'
                   '    Mem.load Mint8unsigned m (sha_symbol_block _tagName__1) (Z.of_nat i) =\n'
                   '      Some (Vint (nth i tapleaf_tag_ints Int.zero)).\n'],
                  ['Coq/C/jet_bitcoin_make_tapbranch_exec.v',
                   'declaration',
                   'sha_tapbranch_tag_ok',
                   'Definition sha_tapbranch_tag_ok (m : mem) : Prop :=\n'
                   '  forall i, (i < 9)%nat ->\n'
                   '    Mem.load Mint8unsigned m (sha_symbol_block _tagName__2) (Z.of_nat i) =\n'
                   '      Some (Vint (nth i tapbranch_tag_ints Int.zero)).\n'],
                  ['Coq/C/jet_sha_uchars_exec.v',
                   'declaration',
                   'sha_max_counter',
                   'Definition sha_max_counter : int64 := Int64.repr 2305843009213693952.\n'],
                  ['Coq/C/jet_memcpy_model.v',
                   'declaration',
                   'memcpy_model',
                   'Definition memcpy_model : Prop :=\n'
                   '  forall (ge : Senv.t) m bd od bs os n bytes,\n'
                   '    Mem.valid_block m bs -> Mem.valid_block m bd ->\n'
                   '    Mem.loadbytes m bs (Ptrofs.unsigned os) n = Some bytes ->\n'
                   '    Mem.range_perm m bd (Ptrofs.unsigned od) (Ptrofs.unsigned od + n) Cur Writable ->\n'
                   '    (bs <> bd \\/ Ptrofs.unsigned os + n <= Ptrofs.unsigned od \\/\n'
                   '      Ptrofs.unsigned od + n <= Ptrofs.unsigned os) ->\n'
                   '    0 < n <= Int64.max_unsigned ->\n'
                   '    Ptrofs.unsigned os + n <= Ptrofs.max_unsigned + 1 ->\n'
                   '    Ptrofs.unsigned od + n <= Ptrofs.max_unsigned + 1 ->\n'
                   "    exists m', Mem.storebytes m bd (Ptrofs.unsigned od) bytes = Some m' /\\\n"
                   '      external_call (EF_external "memcpy" memcpy_sig) ge\n'
                   "        [Vptr bd od; Vptr bs os; Vlong (Int64.repr n)] m E0 (Vptr bd od) m'.\n"
                   '\n'
                   ' \n'
                   '\n'
                   '\n'],
                  ['Coq/C/jet_order_spec.v',
                   'declaration',
                   'lt_word_spec',
                   'Definition lt_word_spec {term : Alg.Core.Algebra} n :\n'
                   '    @Alg.Core.domain term (Ty.Prod (Word n) (Word n)) Bit :=\n'
                   '  AC.comp (@subtract_word_spec term n) (AC.take AC.iden).'],
                  ['Coq/C/jet_core_pad_spec.v',
                   'declaration',
                   'left_pad_low_spec',
                   'Definition left_pad_low_spec {term : Alg.Core.Algebra} (w k : nat) :\n'
                   '    @Alg.Core.domain term (Word w) (Vector (Word w) k) :=\n'
                   '  left_pad_pad (AC.comp AC.unit (low_word w)) k.'],
                  ['Coq/C/jet_sha_tapdata_spec.v',
                   'statement',
                   'tag_hash_eval',
                   'Lemma tag_hash_eval : @Simplicity.SHA256.hashBlock Alg.CoreFunSem (iv_word, tag_block) = '
                   'tag_word.\n'],
                  ['Coq/C/jet_sha_tapdata_spec.v',
                   'statement',
                   'tapdata_prefix_eval',
                   'Lemma tapdata_prefix_eval :\n'
                   '  @Simplicity.SHA256.hashBlock Alg.CoreFunSem (iv_word, (tag_word, tag_word)) = '
                   'tapdata_prefix.\n'],
                  ['Coq/C/jet_sha_tapdata_spec.v',
                   'statement',
                   'tag_block_bytes',
                   'Lemma tag_block_bytes :\n'
                   '  map Int.unsigned (map word8_array_value (vector_values (Word 3) 6 tag_block)) =\n'
                   '  map Int.unsigned (tag_bytes ++ sha_pad (Int64.repr 7)).\n'],
                  ['Coq/C/jet_sha_tapdata_spec.v',
                   'statement',
                   'iv_word_regs',
                   'Lemma iv_word_regs : state_regs iv_word = sha256_iv_words.\n'],
                  ['Coq/C/jet_bitcoin_tapleaf_hash_spec.v',
                   'statement',
                   'tapleaf_tag_hash_eval',
                   'Lemma tapleaf_tag_hash_eval :\n'
                   '  @Simplicity.SHA256.hashBlock Alg.CoreFunSem (iv_word, tapleaf_tag_block) = '
                   'tapleaf_tag_word.\n'],
                  ['Coq/C/jet_bitcoin_tapleaf_hash_spec.v',
                   'statement',
                   'tapleaf_prefix_eval',
                   'Lemma tapleaf_prefix_eval :\n'
                   '  @Simplicity.SHA256.hashBlock Alg.CoreFunSem (iv_word, (tapleaf_tag_word, '
                   'tapleaf_tag_word)) = tapleaf_prefix.\n'],
                  ['Coq/C/jet_bitcoin_tapleaf_hash_spec.v',
                   'statement',
                   'tapleaf_tag_block_bytes',
                   'Lemma tapleaf_tag_block_bytes :\n'
                   '  map Int.unsigned (map word8_array_value (vector_values (Word 3) 6 tapleaf_tag_block)) '
                   '=\n'
                   '  map Int.unsigned (tapleaf_tag_bytes ++ sha_pad (Int64.repr 7)).\n'],
                  ['Coq/C/jet_bitcoin_build_tapbranch_spec.v',
                   'statement',
                   'tapbranch_tag_hash_eval',
                   'Lemma tapbranch_tag_hash_eval :\n'
                   '  @Simplicity.SHA256.hashBlock Alg.CoreFunSem (iv_word, tapbranch_tag_block) = '
                   'tapbranch_tag_word.\n'],
                  ['Coq/C/jet_bitcoin_build_tapbranch_spec.v',
                   'statement',
                   'tapbranch_prefix_eval',
                   'Lemma tapbranch_prefix_eval :\n'
                   '  @Simplicity.SHA256.hashBlock Alg.CoreFunSem (iv_word, (tapbranch_tag_word, '
                   'tapbranch_tag_word)) =\n'
                   '    tapbranch_prefix.\n'],
                  ['Coq/C/jet_bitcoin_build_tapbranch_spec.v',
                   'statement',
                   'tapbranch_tag_block_bytes',
                   'Lemma tapbranch_tag_block_bytes :\n'
                   '  map Int.unsigned (map word8_array_value (vector_values (Word 3) 6 '
                   'tapbranch_tag_block)) =\n'
                   '  map Int.unsigned (tapbranch_tag_bytes ++ sha_pad (Int64.repr 9)).\n'],
                  ['Coq/C/jet_bitcoin_build_tapbranch_spec.v',
                   'statement',
                   'tb_padblock_words',
                   'Lemma tb_padblock_words :\n'
                   '  map Int.unsigned (map word32_array_value (word32_chunks 4 tb_padblock)) =\n'
                   '  map Int.unsigned (be_words (sha_pad (Int64.repr 128))).\n'],
                  ['Coq/C/jet_sha_canonical_startup.v',
                   'statement',
                   'sha_canonical_startup_nonvacuous',
                   'Theorem sha_canonical_startup_nonvacuous :\n'
                   '  exists m, Genv.init_mem jets_sha.prog = Some m /\\ sha_startup_state m.\n'],
                  ['Coq/C/jet_sha_canonical_startup.v',
                   'statement',
                   'sha_256_block_canonical_startup_spec',
                   'Theorem sha_256_block_canonical_startup_spec :\n'
                   '  sha_startup_total_spec f_simplicity_sha_256_block (Ty.Prod Word256 Word512) Word256\n'
                   '    (@Simplicity.SHA256.hashBlock Alg.CoreFunSem).\n'],
                  ['Coq/C/jet_sha_canonical_startup.v',
                   'statement',
                   'sha_256_ctx_8_add_1_canonical_startup_spec',
                   'Theorem sha_256_ctx_8_add_1_canonical_startup_spec : memcpy_model ->\n'
                   '  sha_startup_partial_spec f_simplicity_sha_256_ctx_8_add_1\n'
                   '    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 0)) sha256_ctx8_type\n'
                   '    (fun a => @ctx8_addn_spec 0 optalg a).\n'],
                  ['Coq/C/jet_sha_canonical_startup.v',
                   'statement',
                   'sha_256_ctx_8_add_2_canonical_startup_spec',
                   'Theorem sha_256_ctx_8_add_2_canonical_startup_spec : memcpy_model ->\n'
                   '  sha_startup_partial_spec f_simplicity_sha_256_ctx_8_add_2\n'
                   '    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 1)) sha256_ctx8_type\n'
                   '    (fun a => @ctx8_addn_spec 1 optalg a).\n'],
                  ['Coq/C/jet_sha_canonical_startup.v',
                   'statement',
                   'sha_256_ctx_8_add_4_canonical_startup_spec',
                   'Theorem sha_256_ctx_8_add_4_canonical_startup_spec : memcpy_model ->\n'
                   '  sha_startup_partial_spec f_simplicity_sha_256_ctx_8_add_4\n'
                   '    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 2)) sha256_ctx8_type\n'
                   '    (fun a => @ctx8_addn_spec 2 optalg a).\n'],
                  ['Coq/C/jet_sha_canonical_startup.v',
                   'statement',
                   'sha_256_ctx_8_add_8_canonical_startup_spec',
                   'Theorem sha_256_ctx_8_add_8_canonical_startup_spec : memcpy_model ->\n'
                   '  sha_startup_partial_spec f_simplicity_sha_256_ctx_8_add_8\n'
                   '    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 3)) sha256_ctx8_type\n'
                   '    (fun a => @ctx8_addn_spec 3 optalg a).\n'],
                  ['Coq/C/jet_sha_canonical_startup.v',
                   'statement',
                   'sha_256_ctx_8_add_16_canonical_startup_spec',
                   'Theorem sha_256_ctx_8_add_16_canonical_startup_spec : memcpy_model ->\n'
                   '  sha_startup_partial_spec f_simplicity_sha_256_ctx_8_add_16\n'
                   '    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 4)) sha256_ctx8_type\n'
                   '    (fun a => @ctx8_addn_spec 4 optalg a).\n'],
                  ['Coq/C/jet_sha_canonical_startup.v',
                   'statement',
                   'sha_256_ctx_8_add_32_canonical_startup_spec',
                   'Theorem sha_256_ctx_8_add_32_canonical_startup_spec : memcpy_model ->\n'
                   '  sha_startup_partial_spec f_simplicity_sha_256_ctx_8_add_32\n'
                   '    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 5)) sha256_ctx8_type\n'
                   '    (fun a => @ctx8_addn_spec 5 optalg a).\n'],
                  ['Coq/C/jet_sha_canonical_startup.v',
                   'statement',
                   'sha_256_ctx_8_add_64_canonical_startup_spec',
                   'Theorem sha_256_ctx_8_add_64_canonical_startup_spec : memcpy_model ->\n'
                   '  sha_startup_partial_spec f_simplicity_sha_256_ctx_8_add_64\n'
                   '    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 6)) sha256_ctx8_type\n'
                   '    (fun a => @ctx8_addn_spec 6 optalg a).\n'],
                  ['Coq/C/jet_sha_canonical_startup.v',
                   'statement',
                   'sha_256_ctx_8_add_128_canonical_startup_spec',
                   'Theorem sha_256_ctx_8_add_128_canonical_startup_spec : memcpy_model ->\n'
                   '  sha_startup_partial_spec f_simplicity_sha_256_ctx_8_add_128\n'
                   '    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 7)) sha256_ctx8_type\n'
                   '    (fun a => @ctx8_addn_spec 7 optalg a).\n'],
                  ['Coq/C/jet_sha_canonical_startup.v',
                   'statement',
                   'sha_256_ctx_8_add_256_canonical_startup_spec',
                   'Theorem sha_256_ctx_8_add_256_canonical_startup_spec : memcpy_model ->\n'
                   '  sha_startup_partial_spec f_simplicity_sha_256_ctx_8_add_256\n'
                   '    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 8)) sha256_ctx8_type\n'
                   '    (fun a => @ctx8_addn_spec 8 optalg a).\n'],
                  ['Coq/C/jet_sha_canonical_startup.v',
                   'statement',
                   'sha_256_ctx_8_add_512_canonical_startup_spec',
                   'Theorem sha_256_ctx_8_add_512_canonical_startup_spec : memcpy_model ->\n'
                   '  sha_startup_partial_spec f_simplicity_sha_256_ctx_8_add_512\n'
                   '    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 9)) sha256_ctx8_type\n'
                   '    (fun a => @ctx8_addn_spec 9 optalg a).\n'],
                  ['Coq/C/jet_sha_canonical_startup.v',
                   'statement',
                   'sha_256_ctx_8_add_buffer_511_canonical_startup_spec',
                   'Theorem sha_256_ctx_8_add_buffer_511_canonical_startup_spec : memcpy_model ->\n'
                   '  sha_startup_partial_spec f_simplicity_sha_256_ctx_8_add_buffer_511\n'
                   '    (Ty.Prod sha256_ctx8_type (buffer_type (Word 3) 8)) sha256_ctx8_type\n'
                   '    (fun a => @ctx8_add_buffer_spec 8 optalg a).\n'],
                  ['Coq/C/jet_sha_canonical_startup.v',
                   'statement',
                   'sha_256_ctx_8_finalize_canonical_startup_spec',
                   'Theorem sha_256_ctx_8_finalize_canonical_startup_spec : memcpy_model ->\n'
                   '  sha_startup_partial_spec f_simplicity_sha_256_ctx_8_finalize sha256_ctx8_type (Word '
                   '8)\n'
                   '    (fun a => @ctx8_finalize_spec optalg a).\n'],
                  ['Coq/C/jet_sha_canonical_startup.v',
                   'statement',
                   'tapdata_init_canonical_startup_spec',
                   'Theorem tapdata_init_canonical_startup_spec : memcpy_model ->\n'
                   '  sha_startup_total_spec f_simplicity_tapdata_init Ty.Unit sha256_ctx8_type\n'
                   '    (fun a => @tapdata_init_spec Alg.CoreFunSem a).\n'],
                  ['Coq/C/jet_sha_canonical_startup.v',
                   'statement',
                   'bitcoin_annex_hash_canonical_startup_spec',
                   'Theorem bitcoin_annex_hash_canonical_startup_spec : memcpy_model ->\n'
                   '  sha_startup_partial_spec f_simplicity_bitcoin_annex_hash\n'
                   '    (Ty.Prod sha256_ctx8_type (Ty.Sum Ty.Unit (Word 8))) sha256_ctx8_type\n'
                   '    (fun a => @annex_hash_spec optalg a).\n'],
                  ['Coq/C/jet_sha_canonical_startup.v',
                   'statement',
                   'bitcoin_outpoint_hash_canonical_startup_spec',
                   'Theorem bitcoin_outpoint_hash_canonical_startup_spec : memcpy_model ->\n'
                   '  sha_startup_partial_spec f_simplicity_bitcoin_outpoint_hash\n'
                   '    (Ty.Prod sha256_ctx8_type (Ty.Prod (Word 8) (Word 5))) sha256_ctx8_type\n'
                   '    (fun a => @outpoint_hash_spec optalg a).\n'],
                  ['Coq/C/jet_sha_canonical_startup.v',
                   'statement',
                   'bitcoin_build_tapleaf_simplicity_canonical_startup_spec',
                   'Theorem bitcoin_build_tapleaf_simplicity_canonical_startup_spec : memcpy_model ->\n'
                   '  sha_startup_total_spec f_simplicity_bitcoin_build_tapleaf_simplicity\n'
                   '    (Word 8) (Word 8) (fun a => @build_tapleaf_spec Alg.CoreFunSem a).\n'],
                  ['Coq/C/jet_sha_canonical_startup.v',
                   'statement',
                   'bitcoin_build_tapbranch_canonical_startup_spec',
                   'Theorem bitcoin_build_tapbranch_canonical_startup_spec : memcpy_model ->\n'
                   '  sha_startup_total_spec f_simplicity_bitcoin_build_tapbranch\n'
                   '    (Word 9) (Word 8) (fun ab => @build_tapbranch_spec Alg.CoreFunSem ab).\n'],
                  ['Coq/Simplicity/Word.v',
                   'declaration',
                   'fill',
                   'Fixpoint fill {C X n} {term : Core.Algebra} (t : term C X) : term C (Vector X n) :=\n'
                   'match n with\n'
                   '| 0 => t\n'
                   '| (S n) => build_fill (fill t)\n'
                   'end.\n'],
                  ['Coq/Simplicity/Word.v',
                   'declaration',
                   'leftmost',
                   'Fixpoint leftmost {X n} {term : Core.Algebra} : term (Vector X n) X :=\n'
                   'match n with\n'
                   '| 0 => iden\n'
                   '| S n => build_leftmost leftmost\n'
                   'end.\n'],
                  ['Coq/Simplicity/Word.v',
                   'declaration',
                   'rightmost',
                   'Fixpoint rightmost {X n} {term : Core.Algebra} : term (Vector X n) X :=\n'
                   'match n with\n'
                   '| 0 => iden\n'
                   '| S n => build_rightmost rightmost\n'
                   'end.\n'],
                  ['Coq/Simplicity/Word.v',
                   'declaration',
                   'full_left_shift1',
                   'Fixpoint full_left_shift1 {X n} {term : Core.Algebra} :\n'
                   '  term (Vector X n * X) (X * Vector X n) :=\n'
                   'match n with\n'
                   '| 0 => iden\n'
                   '| S n => build_full_left_shift1 full_left_shift1\n'
                   'end.\n'],
                  ['Coq/Simplicity/Word.v',
                   'declaration',
                   'full_right_shift1',
                   'Fixpoint full_right_shift1 {X n} {term : Core.Algebra} :\n'
                   '  term (X * Vector X n) (Vector X n * X) :=\n'
                   'match n with\n'
                   '| 0 => iden\n'
                   '| S n => build_full_right_shift1 full_right_shift1\n'
                   'end.\n'],
                  ['Coq/Simplicity/Word.v',
                   'declaration',
                   'left_shift1',
                   'Definition left_shift1 {X n} {term : Core.Algebra} (t : term Unit X) : term (Vector X n) '
                   '(Vector X n) :=\n'
                   'iden &&& (unit >>> t) >>> full_left_shift1 >>> I H.\n'],
                  ['Coq/Simplicity/Word.v',
                   'declaration',
                   'right_shift1',
                   'Definition right_shift1 {X n} {term : Core.Algebra} (t : term Unit X) : term (Vector X '
                   'n) (Vector X n) :=\n'
                   '(unit >>> t) &&& iden >>> full_right_shift1 >>> O H.\n'],
                  ['Coq/Simplicity/Word.v',
                   'declaration',
                   'left_shift_const_by',
                   'Fixpoint left_shift_const_by {X n} {term : Core.Algebra} (t : term Unit X) (p : '
                   'positive) \n'
                   ' : term (Vector X n) (Vector X n) :=\n'
                   'if (Zpower_nat 2 n <=? Zpos p)%Z then\n'
                   ' unit >>> fill t else\n'
                   'match n with \n'
                   '| 0 => iden\n'
                   '| (S n0) => match p with\n'
                   '  | xH => left_shift1 t\n'
                   '  | xO p0 => eq_rect _ (fun x => term x x) (left_shift_const_by (t &&& t) p0) _ (eq_sym '
                   'VectorPromote)\n'
                   '  | xI p0 => left_shift1 t >>> eq_rect _ (fun x => term x x) (left_shift_const_by (t &&& '
                   't) p0) _ (eq_sym VectorPromote)\n'
                   '  end\n'
                   'end.\n'],
                  ['Coq/Simplicity/Word.v',
                   'declaration',
                   'right_shift_const_by',
                   'Fixpoint right_shift_const_by {X n} {term : Core.Algebra} (t : term Unit X) (p : '
                   'positive) \n'
                   ' : term (Vector X n) (Vector X n) :=\n'
                   'if (Zpower_nat 2 n <=? Zpos p)%Z then\n'
                   ' unit >>> fill t else\n'
                   'match n with \n'
                   '| 0 => iden\n'
                   '| (S n0) => match p with\n'
                   '  | xH => right_shift1 t\n'
                   '  | xO p0 => eq_rect _ (fun x => term x x) (right_shift_const_by (t &&& t) p0) _ (eq_sym '
                   'VectorPromote)\n'
                   '  | xI p0 => right_shift1 t >>> eq_rect _ (fun x => term x x) (right_shift_const_by (t '
                   '&&& t) p0) _ (eq_sym VectorPromote)\n'
                   '  end\n'
                   'end.\n'],
                  ['Coq/C/jet_core_pad_spec.v',
                   'declaration',
                   'left_pad_pad',
                   'Fixpoint left_pad_pad {term : Alg.Core.Algebra} {a} (t : @Alg.Core.domain term a a) (k : '
                   'nat) :\n'
                   '    @Alg.Core.domain term a (Vector a k) :=\n'
                   '  match k with\n'
                   '  | O => AC.iden\n'
                   '  | S k => AC.pair (fill (n := k) t) (left_pad_pad t k)\n'
                   '  end.\n'],
                  ['Coq/C/jet_core_pad_spec.v',
                   'declaration',
                   'low_word',
                   'Definition low_word {term : Alg.Core.Algebra} (w : nat) : @Alg.Core.domain term Ty.Unit '
                   '(Word w) :=\n'
                   '  fill (n := w) (@Bit.false Ty.Unit term).'],
                  ['Coq/C/jet_spec.v',
                   'declaration',
                   'left_pad_low_1_n',
                   'Fixpoint left_pad_low_1_n {term : Alg.Core.Algebra} (n : nat) :\n'
                   '    @Alg.Core.domain term Bit (Word n) :=\n'
                   '  match n with\n'
                   '  | Datatypes.O => @Alg.Core.Combinators.iden Bit term\n'
                   '  | S n =>\n'
                   '      @Alg.Core.Combinators.pair Bit (Word n) (Word n) term\n'
                   '        (fill (n := n)\n'
                   '          (@Alg.Core.Combinators.comp Bit Ty.Unit Bit term\n'
                   '            (@Alg.Core.Combinators.unit Bit term) (@Bit.false Ty.Unit term)))\n'
                   '        (left_pad_low_1_n n)\n'
                   '  end.\n'],
                  ['Coq/C/jet_subtract_spec.v',
                   'declaration',
                   'full_subtract_word_spec',
                   'Definition full_subtract_word_spec {term : Alg.Core.Algebra} (n : nat) :\n'
                   '    @Alg.Core.domain term (Ty.Prod Bit (Ty.Prod (Word n) (Word n))) (Ty.Prod Bit (Word '
                   'n)) :=\n'
                   '  AC.comp\n'
                   '    (AC.pair (Bit.not (AC.take AC.iden))\n'
                   '      (AC.drop (AC.pair (AC.take AC.iden) (AC.comp (AC.drop AC.iden) (@complement_spec n '
                   'term)))))\n'
                   '    (AC.comp (@Word.fullAdder n term) (AC.pair (Bit.not (AC.take AC.iden)) (AC.drop '
                   'AC.iden))).'],
                  ['Coq/C/jet_subtract_spec.v',
                   'declaration',
                   'subtract_word_spec',
                   'Definition subtract_word_spec {term : Alg.Core.Algebra} (n : nat) :\n'
                   '    @Alg.Core.domain term (Ty.Prod (Word n) (Word n)) (Ty.Prod Bit (Word n)) :=\n'
                   '  AC.comp (AC.pair Bit.false AC.iden) (@full_subtract_word_spec term n).'],
                  ['Coq/C/jet_complement_spec.v',
                   'declaration',
                   'complement_spec',
                   'Fixpoint complement_spec n {term : Alg.Core.Algebra} :\n'
                   '    @Alg.Core.domain term (Word n) (Word n) :=\n'
                   '  match n with\n'
                   '  | O => @Bit.not Bit term (@Alg.Core.Combinators.iden Bit term)\n'
                   '  | S n => @Alg.Core.Combinators.pair (Word (S n)) (Word n) (Word n) term\n'
                   '      (@Alg.Core.Combinators.take (Word n) (Word n) (Word n) term (complement_spec n))\n'
                   '      (@Alg.Core.Combinators.drop (Word n) (Word n) (Word n) term (complement_spec n))\n'
                   '  end.\n']],
 'blocks': [['Haskell/Core/Simplicity/Programs/Sha256.hs',
             'lib = l\n',
             'hashLoop ::',
             ' where\n'
             '  l@Lib{..} = Lib\n'
             '   { iv = scribe . toWord256 $ '
             '0x6a09e667bb67ae853c6ef372a54ff53a510e527f9b05688c1f83d9ab5be0cd19\n'
             '   , hashBlock = oh &&& compression\n'
             '             >>> ((collate oooh &&& collate ooih)\n'
             '             &&&  (collate oioh &&& collate oiih))\n'
             '             &&& ((collate iooh &&& collate ioih)\n'
             '             &&&  (collate iioh &&& collate iiih))\n'
             '   , ctx8Init = buffer63Empty &&& (zero word64 &&& iv)\n'
             '   , tapdataInit = buffer63Empty &&& (one word64 &&& tapdataPrefix)\n'
             '   }\n'
             '   where\n'
             '    collate x = take x &&& drop x >>> add32\n'
             '    compression = scribe32 k0 &&& iden >>> foldr (\\k rec -> scribe32 k &&& step >>> rec) '
             'round ks\n'
             '    k0:ks = [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, '
             '0x923f82a4, 0xab1c5ed5\n'
             '            ,0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, '
             '0x9bdc06a7, 0xc19bf174\n'
             '            ,0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, '
             '0x5cb0a9dc, 0x76f988da\n'
             '            ,0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, '
             '0x06ca6351, 0x14292967\n'
             '            ,0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, '
             '0x81c2c92e, 0x92722c85\n'
             '            ,0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, '
             '0xf40e3585, 0x106aa070\n'
             '            ,0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, '
             '0x5b9cca4f, 0x682e6ff3\n'
             '            ,0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, '
             '0xbef9a3f7, 0xc67178f2]\n'
             '    step = round &&& (drop (drop schedule))\n'
             '    scribe32 x = scribe (toWord32 x)\n'
             '    round = part1 >>> part2\n'
             '     where\n'
             '      part1 = ((t1 &&& io oooh) &&& io odiag)\n'
             '          &&& io (bigDiag &&& idiag)\n'
             '      part2 = ((t12 &&& ooih) &&& oih)\n'
             '          &&& ((t1d &&& ioih) &&& iih)\n'
             '      t1 = (oh &&& iio oooh >>> add32) &&& io (drop (iih &&& ((ooh >>> bigSigma1) &&& (ooh &&& '
             'diag >>> chWord32) >>> add32)) >>> add32) >>> add32\n'
             '      t12 = take ((oih &&& ih >>> majWord32) &&& (take (oh &&& (ih >>> bigSigma0)) >>> add32)) '
             '>>> add32\n'
             '      t1d = oooh &&& iooh >>> add32\n'
             '      bigSigma0 = rotateW32 (-2) &&& rotateW32 (-13) &&& rotateW32 (-22) >>> xor_xorWord32\n'
             '      bigSigma1 = rotateW32 (-6) &&& rotateW32 (-11) &&& rotateW32 (-25) >>> xor_xorWord32\n'
             '      chWord32 = bitwise_ch word32\n'
             '      majWord32 = bitwise_maj word32\n'
             '    schedule = (take part1 &&& (take idiag &&& (take iiih &&& drop oooh)))\n'
             '           &&& (drop part1 &&& (drop idiag &&& (drop iiih &&& smallSigma)))\n'
             '     where\n'
             '      part1 = odiag &&& bigDiag\n'
             '      smallSigma = (take (oo (oh &&& (ih >>> smallSigma0))) >>> add32) &&& (drop (ooih &&& '
             '(iioh >>> smallSigma1)) >>> add32) >>> add32\n'
             '      smallSigma0 = rotateW32 (-7)  &&& rotateW32 (-18) &&& shiftW32 (-3)  >>> xor_xorWord32\n'
             '      smallSigma1 = rotateW32 (-17) &&& rotateW32 (-19) &&& shiftW32 (-10) >>> xor_xorWord32\n'
             '    oo x = take (take x)\n'
             '    io x = drop (take x)\n'
             '    iio x = drop (io x)\n'
             '    diag = oih &&& ioh\n'
             '    odiag = take diag\n'
             '    idiag = drop diag\n'
             '    bigDiag = oiih &&& iooh\n'
             '    add32 = add word32 >>> ih\n'
             '    xor_xorWord32 = bitwise_xor_xor word32\n'
             '    rotateW32 = rotate_const word32\n'
             '    shiftW32 = shift_const_by false word32\n'
             '    buffer63Empty = bufferEmpty buffer63\n'
             '    tapdataPrefix = scribe . toWord256 . integerHash256 . ivHash . tagIv $ fromString '
             '"TapData"\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'],
            ['Haskell/Core/Simplicity/Programs/Sha256.hs',
             'mkLibAssert Lib{..}  = l\n',
             'libAssert ::',
             ' where\n'
             '  l@LibAssert{..} = LibAssert\n'
             '   { ctx8Add1 = (ooh &&& ih >>> buffer63Snoc) &&& oih\n'
             '            >>> match ((unit >>> buffer63Empty) &&& ((drop (take (increment word64) >>> '
             'assertl ih cmrFail0)) &&& (iih &&& oh >>> hashBlock)))\n'
             '                      iden\n'
             '            >>> (verifyNumCompression &&& iden) >>> ih\n'
             '   , ctx8Addn = \\v -> case v of\n'
             '                  SingleV -> ctx8Add1\n'
             '                  (DoubleV v) -> let rec = ctx8Addn v in\n'
             '                                 (oh &&& ioh >>> rec) &&& iih >>> rec\n'
             '   , ctx8AddBuffer = \\b -> case b of\n'
             '                       SingleB -> ih &&& oh >>> match (drop (iden &&& verifyNumCompression >>> '
             'oh)) (ih &&& oh >>> ctx8Add1)\n'
             '                       (DoubleB b) -> (ioh &&& oh >>> match ih (ih &&& oh >>> ctx8Addn '
             '(bufferVector b))) &&& iih >>> ctx8AddBuffer b\n'
             '     \n'
             '   , ctx8Finalize = ((oh &&& ((verifyNumCompression >>> zero word64) &&& iih)) &&& (unit >>> '
             'scribe (toWord64 (2^63))) >>> ctx8Add8 >>> (take pad063 &&& iih))\n'
             '                &&& ((take buffer63Size >>> left_pad_low word8 vector8) &&& drop (take '
             '(shift_const_by false word64 6)) >>> add64 >>> shift_const_by false word64 3)\n'
             '                >>> oih &&& (oooh &&& (take oioh &&& (take (take iioh) &&& ih))) >>> '
             'hashBlock\n'
             '   }\n'
             '   where\n'
             '    buffer63Empty = bufferEmpty buffer63\n'
             '    ctx8Add8 = ctx8Addn vector8\n'
             '    verifyNumCompression = assert (ioh &&& (unit >>> scribe (toWord64 (2^55))) >>> lt word64)\n'
             '    add64 = add word64 >>> ih\n'
             '    buffer63Snoc = bufferSnoc buffer63\n'
             '    buffer63Size = ((false &&& false) &&& (take (copair false true) &&& drop (take (copair '
             'false true))))\n'
             '               &&& drop (drop ((take (copair false true) &&& drop (take (copair false true))) '
             '&&& drop (drop (take (copair false true) &&& drop (copair false true)))))\n'
             '    pad063 = oh &&& drop pad031 >>> match (ih &&& take (zero word256)) iden\n'
             '    pad031 = oh &&& drop pad015 >>> match (ih &&& take (zero word128)) iden\n'
             '    pad015 = oh &&& drop pad07 >>> match (ih &&& take (zero word64)) iden\n'
             '    pad07 = oh &&& drop pad03 >>> match (ih &&& take (zero word32)) iden\n'
             '    pad03 = oh &&& drop pad01 >>> match (ih &&& take (zero word16)) iden\n'
             '    pad01 = copair (zero word16) (iden &&& (unit >>> zero word8))\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'],
            ['Haskell/Core/Simplicity/Programs/Bitcoin.hs',
             'mkLib Sha256.Lib{..} = lib\n',
             'lib ::',
             ' where\n'
             '  lib@Lib{..} = Lib {\n'
             '    buildTapleafSimplicity = (unit >>> tapleafPrefix)\n'
             '                         &&& ((unit >>> (simplicityVersion &&& scribe (toWord8 32))) &&& iden '
             '>>> full_shift word16 word256 >>>\n'
             '                              (oh &&& ((((ih &&& (unit >>> scribe (toWord16 0x8000))) &&& '
             '(unit >>> zero word32)) &&& (unit >>> zero word64)) &&& (unit >>> scribe (toWord128 '
             '(512+16+256))))))\n'
             '                         >>> hashBlock\n'
             '  , buildTapbranch = ((unit >>> tapbranchPrefix)\n'
             '                 &&& (lt word256 &&& iden >>> cond iden (ih &&& oh))\n'
             '                 >>> hashBlock)\n'
             '                 &&& (unit >>> scribe (toWord512 $ 2^511 + 1024)) >>> hashBlock\n'
             '  } where\n'
             '    tapleafPrefix = scribe . toWord256 . integerHash256 . ivHash . tagIv $ fromString '
             '"TapLeaf"\n'
             '    tapbranchPrefix = scribe . toWord256 . integerHash256 . ivHash . tagIv $ fromString '
             '"TapBranch"\n'
             '    simplicityVersion = scribe . toWord8 $ 0xbe\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'],
            ['Haskell/Core/Simplicity/Programs/Bitcoin.hs',
             'mkLibAssert Sha256.Lib{..} Sha256.LibAssert{..} LibSecp256k1.Lib{..} = libAssert\n',
             'libAssert ::',
             ' where\n'
             '  libAssert@LibAssert{..} = LibAssert {\n'
             '    outpointHash = (oh &&& ioh >>> ctx8Add32) &&& iih >>> ctx8Add4\n'
             '  , annexHash = ih &&& oh\n'
             '            >>> match (ih &&& take (zero word8) >>> ctx8Add1)\n'
             '                      ((ih &&& (unit >>> scribe (toWord8 0x01)) >>> ctx8Add1) &&& oh >>> '
             'ctx8Add32)\n'
             '  , buildTaptweak = assert (\n'
             '                  (((assert (oh &&& (unit >>> scribe (toWord256 fieldOrder)) >>> lt256) >>> '
             'taptweakPrefix) &&& iden >>> hashBlock)\n'
             '                &&& (unit >>> scribe (toWord512 $ 2^511 + 1024)) >>> hashBlock >>>\n'
             '                   (assert (iden &&& (unit >>> scribe (toWord256 groupOrder)) >>> lt256) &&& '
             'iden) >>> drop generate)\n'
             '                &&& assert ((unit >>> false) &&& oh >>> decompress)\n'
             '                >>> gej_ge_add >>> gej_normalize) >>> oh\n'
             '  } where\n'
             '    lt256 = lt word256\n'
             '    ctx8Add32 = ctx8Addn vector32\n'
             '    ctx8Add8 = ctx8Addn vector8\n'
             '    ctx8Add4 = ctx8Addn vector4\n'
             '    taptweakPrefix = scribe . toWord256 . integerHash256 . ivHash . tagIv $ fromString '
             '"TapTweak"\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'],
            ['Haskell/Core/Simplicity/Programs/Word.hs',
             'bufferEmpty ::',
             'forWhile ::',
             ' (Core term, TyC e) => Buffer x v b -> term e b\n'
             'bufferEmpty SingleB = injl unit\n'
             'bufferEmpty (DoubleB b) = injl unit &&& bufferEmpty b\n'
             '\n'
             '\n'
             '\n'
             '\n'
             'bufferSnoc :: Core term => Buffer x v b -> term (b, x) (Either v b)\n'
             'bufferSnoc SingleB = match (injr (injr ih)) (injl iden)\n'
             'bufferSnoc (DoubleB b) = (oih &&& ih >>> bufferSnoc b) &&& ooh\n'
             '                     >>> match (ih &&& oh >>> match (injr (injr ih &&& bufferEmpty b)) (injl '
             'iden))\n'
             '                               (injr (ih &&& oh))\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'],
            ['Haskell/Core/Simplicity/Programs/Word.hs',
             'rotate_const ::',
             'left_rotate ::',
             ' (Core term, TyC a, TyC b) => Vector a b -> Int -> term b b\n'
             'rotate_const v n = compose (go v n)\n'
             ' where\n'
             '  compose [] = iden\n'
             '  compose l = foldr1 (>>>) l\n'
             '  go :: (Core term, TyC a, TyC b) => Vector a b -> Int -> [term b b]\n'
             '  go SingleV n = []\n'
             "  go v@(DoubleV v') n | even n = rec (n `div` 2)\n"
             '                      | 1 == n `mod` 4 = left_rotate1 v : rec ((n-1) `div` 2)\n'
             '                      | 3 == n `mod` 4 = right_rotate1 v : rec ((n+1) `div` 2)\n'
             '   where\n'
             "    rec = go (vectorPromote v')\n"
             '\n'
             '\n'],
            ['Haskell/Core/Simplicity/Programs/Arith.hs',
             '\nfull_add ::',
             '\nadd ::',
             ' Core term => Word a -> term (Bit, (a, a)) (Bit, a)\n'
             'full_add SingleV = maj &&& xor_xor\n'
             'full_add (DoubleV w) = drop (ooh &&& ioh) &&& (oh &&& drop (oih &&& iih) >>> rec)\n'
             '                   >>> iih &&& (ioh &&& oh >>> rec)\n'
             '                   >>> ioh &&& (iih &&& oh)\n'
             ' where\n'
             '  rec = full_add w\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'],
            ['Haskell/Core/Simplicity/Programs/Arith.hs',
             '\nadd ::',
             '\nfull_increment ::',
             ' (Core term, TyC a) => Word a -> term (a, a) (Bit, a)\n'
             'add w = false &&& iden >>> full_add w\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'],
            ['Haskell/Core/Simplicity/Programs/Arith.hs',
             '\nfull_increment ::',
             '\nfull_subtract ::',
             ' (Core term, TyC a) => Word a -> term (Bit, a) (Bit, a)\n'
             'full_increment w = oh &&& (ih &&& (unit >>> zero w)) >>> full_add w\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'
             'increment :: (Core term, TyC a) => Word a -> term a (Bit, a)\n'
             'increment w = true &&& iden >>> full_increment w\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'],
            ['Haskell/Core/Simplicity/Programs/Bit.hs',
             '\ncond ::',
             '\nnot ::',
             ' (Core term, TyC a, TyC b) => term a b -> term a b -> term (Bit, a) b\n'
             'cond thn els = match (drop els) (drop thn)\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'
             'ch :: (Core term, TyC a) => term (Bit, (a, a)) a\n'
             'ch = cond oh ih\n'
             '\n'
             '\n'
             'assert :: (Assert term, TyC a, TyC b) => term a (Either () b) -> term a b\n'
             'assert t = t &&& unit >>> assertr cmrFail0 oh\n'
             '\n'
             '\n'
             '\n'
             '\n'
             'verify :: (Assert term, TyC a) => term (Either () a) a\n'
             'verify = assert iden\n'
             '\n'],
            ['Haskell/Core/Simplicity/Programs/Bit.hs',
             '\nxor_xor ::',
             '\nmaj ::',
             ' Core term => term (Bit, (Bit, Bit)) Bit\n'
             'xor_xor = cond (cond iden (not iden)) (cond (not iden) iden)\n'
             '\n'],
            ['Haskell/Core/Simplicity/Digest.hs',
             'tagIv ::',
             'freeStart ::',
             ' String -> IV\n'
             'tagIv tag = compress noTagIv (tagDigest, tagDigest)\n'
             ' where\n'
             '  tagDigest = bsHash . BSC.pack $ tag\n'
             '\n'
             '\n'
             'ivHash :: IV -> Hash256\n'
             'ivHash (IV state) =  case pushEndOfInput state of\n'
             '  Done _ _ x -> Hash256 . BSS.toShort . BSL.toStrict . Binary.encode $ x\n'
             '  _          -> error "getHash256 unexpected decoder state"\n'
             '\n'
             '\n'
             '\n'
             '\n'],
            ['Haskell/Core/Simplicity/Digest.hs',
             'bslHash ::',
             'bslDoubleHash ::',
             ' BSL.ByteString -> Hash256\n'
             'bslHash = ivHash . IV . pushChunks sha256Incremental . padSHA1\n'
             '\n'
             '\n'
             'bsHash :: BS.ByteString -> Hash256\n'
             'bsHash = bslHash . BSL.fromStrict\n'
             '\n'
             '\n'],
            ['Haskell/Core/Simplicity/Ty/Word.hs',
             'type Buffer1 x =',
             'buffer1 ::',
             ' S x\n'
             'type Buffer3 x = (S (Vector2 x), Buffer1 x)\n'
             'type Buffer7 x = (S (Vector4 x), Buffer3 x)\n'
             'type Buffer15 x = (S (Vector8 x), Buffer7 x)\n'
             'type Buffer31 x = (S (Vector16 x), Buffer15 x)\n'
             'type Buffer63 x = (S (Vector32 x), Buffer31 x)\n'
             'type Buffer127 x = (S (Vector64 x), Buffer63 x)\n'
             'type Buffer255 x = (S (Vector128 x), Buffer127 x)\n'
             'type Buffer511 x = (S (Vector256 x), Buffer255 x)\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'
             'data Buffer x v b where\n'
             ' SingleB :: TyC x => Buffer x (Vector2 x) (S x)\n'
             ' DoubleB :: (TyC x, TyC v, TyC b) => Buffer x v b -> Buffer x (Vector2 v) (S v, b)\n'
             '\n'],
            ['Haskell/Core/Simplicity/Ty/Word.hs',
             'buffer1 ::',
             'bufferVector  ::',
             ' TyC x => Buffer x (Vector2 x) (Buffer1 x)\n'
             'buffer1 = SingleB\n'
             '\n'
             'buffer3 :: TyC x => Buffer x (Vector4 x) (Buffer3 x)\n'
             'buffer3 = DoubleB buffer1\n'
             '\n'
             'buffer7 :: TyC x => Buffer x (Vector8 x) (Buffer7 x)\n'
             'buffer7 = DoubleB buffer3\n'
             '\n'
             'buffer15 :: TyC x => Buffer x (Vector16 x) (Buffer15 x)\n'
             'buffer15 = DoubleB buffer7\n'
             '\n'
             'buffer31 :: TyC x => Buffer x (Vector32 x) (Buffer31 x)\n'
             'buffer31 = DoubleB buffer15\n'
             '\n'
             'buffer63 :: TyC x => Buffer x (Vector64 x) (Buffer63 x)\n'
             'buffer63 = DoubleB buffer31\n'
             '\n'
             'buffer127 :: TyC x => Buffer x (Vector128 x) (Buffer127 x)\n'
             'buffer127 = DoubleB buffer63\n'
             '\n'
             'buffer255 :: TyC x => Buffer x (Vector256 x) (Buffer255 x)\n'
             'buffer255 = DoubleB buffer127\n'
             '\n'
             'buffer511 :: TyC x => Buffer x (Vector512 x) (Buffer511 x)\n'
             'buffer511 = DoubleB buffer255\n'
             '\n'
             '\n'],
            ['Haskell/Core/Simplicity/Programs/Word.hs',
             '\nfill ::',
             '\nhigh ::',
             ' (Core term, TyC c) => term c a -> Vector a b -> term c b\n'
             'fill t SingleV = t\n'
             'fill t (DoubleV w) = rec &&& rec\n'
             ' where\n'
             '  rec = fill t w\n'
             '\n'
             '\n'
             'low :: Core term => Word a -> term () a\n'
             'low = fill false\n'
             '\n'],
            ['Haskell/Core/Simplicity/Programs/Word.hs',
             '\ncomplement ::',
             '\nbitwise_bin ::',
             ' Core term => Word a -> term a a\n'
             'complement SingleV = not iden\n'
             'complement (DoubleV w) = take rec &&& drop rec\n'
             ' where\n'
             '  rec = complement w\n'
             '\n'],
            ['Haskell/Core/Simplicity/Programs/Word.hs',
             '\nbitwise_tri ::',
             '\nbitwise_and ::',
             ' forall term a v. Core term => term (a, (a, a)) a -> Vector a v -> term (v, (v, v)) v\n'
             'bitwise_tri op = go\n'
             ' where\n'
             '  go :: forall v. Vector a v -> term (v, (v, v)) v\n'
             '  go SingleV = op\n'
             '  go (DoubleV w) = (ooh &&& (iooh &&& iioh) >>> rec) &&& (oih &&& (ioih &&& iiih) >>> rec)\n'
             '   where\n'
             '    rec = go w\n'
             '\n'],
            ['Haskell/Core/Simplicity/Programs/Word.hs',
             '\nleftmost ::',
             '\nleft_pad_high ::',
             ' (Core term, TyC a, TyC b) => Vector a b -> term b a\n'
             'leftmost SingleV = iden\n'
             'leftmost (DoubleV v) = take (leftmost v)\n'
             '\n'
             '\n'
             '\n'
             '\n'
             'rightmost :: (Core term, TyC a, TyC b) => Vector a b -> term b a\n'
             'rightmost SingleV = iden\n'
             'rightmost (DoubleV v) = drop (rightmost v)\n'
             '\n'
             '\n'
             'left_pad_pad :: Core term => term a a -> Vector a b -> term a b\n'
             'left_pad_pad _ SingleV = iden\n'
             'left_pad_pad t (DoubleV v) = fill t v &&& left_pad_pad t v\n'
             '\n'
             '\n'
             'left_pad_low :: (Core term, TyC a) => Word a -> Vector a b -> term a b\n'
             'left_pad_low w v = left_pad_pad (unit >>> low w) v\n'
             '\n'],
            ['Haskell/Core/Simplicity/Programs/Word.hs',
             '\nfull_left_shift1 ::',
             '\nitemsOf ::',
             ' Core term => Vector a va -> term (va, a) (a, va)\n'
             'full_left_shift1 SingleV = iden\n'
             'full_left_shift1 (DoubleV v) = ooh &&& (oih &&& ih >>> rec) >>> (oh &&& ioh >>> rec) &&& iih '
             '>>> ooh &&& (oih &&& ih)\n'
             ' where\n'
             '  rec = full_left_shift1 v\n'
             '\n'
             '\n'
             'full_right_shift1 :: Core term => Vector a va -> term (a, va) (va, a)\n'
             'full_right_shift1 SingleV = iden\n'
             'full_right_shift1 (DoubleV v) = (oh &&& ioh >>> rec) &&& iih >>> ooh &&& (oih &&& ih >>> rec) '
             '>>> (oh &&& ioh) &&& iih\n'
             ' where\n'
             '  rec = full_right_shift1 v\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'
             'full_shift :: (Core term, TyC a, TyC b) => Vector x a -> Vector x b -> term (a, b) (b, a)\n'
             'full_shift wa wb = go (compareVectorSize wb wa)\n'
             ' where\n'
             '  go :: (Core term, TyC a, TyC b) => Either (Vector (a, a) b) (Either (b :~: a) (Vector (b, b) '
             'a)) -> term (a, b) (b, a)\n'
             '  go (Left v) = full_right_shift1 (vectorComp vector2 v)\n'
             '  go (Right (Left Refl)) = iden\n'
             '  go (Right (Right v)) = full_left_shift1 (vectorComp vector2 v)\n'
             '\n'
             '\n'
             '\n'
             'shift_const_by :: (Core term, TyC a, TyC b) => term () a -> Vector a b -> Int -> term b b\n'
             'shift_const_by t v n | vectorSize v <= n = unit >>> fill t v\n'
             '                     | n < 0 = right_shift_const_by t v (-n)\n'
             '                     | otherwise = compose (go t v n)\n'
             ' where\n'
             '  compose [] = iden\n'
             '  compose l = foldr1 (>>>) l\n'
             '  go :: (Core term, TyC a, TyC b) => term () a -> Vector a b -> Int -> [term b b]\n'
             '  go t SingleV 0 = []\n'
             "  go t v@(DoubleV v') n | even n = rec (n `div` 2)\n"
             '                        | otherwise = left_shift1 : rec ((n-1) `div` 2)\n'
             '   where\n'
             '    left_shift1 = iden &&& (unit >>> t) >>> full_left_shift1 v >>> ih\n'
             "    rec = go (t &&& t) (vectorPromote v')\n"
             '\n'
             '\n'
             '\n'
             'right_shift_const_by :: (Core term, TyC a, TyC b) => term () a -> Vector a b -> Int -> term b '
             'b\n'
             'right_shift_const_by t v n | vectorSize v <= n = unit >>> fill t v\n'
             '                           | n < 0 = shift_const_by t v (-n)\n'
             '                           | otherwise = compose (go t v n)\n'
             ' where\n'
             '  compose [] = iden\n'
             '  compose l = foldr1 (>>>) l\n'
             '  go :: (Core term, TyC a, TyC b) => term () a -> Vector a b -> Int -> [term b b]\n'
             '  go t SingleV 0 = []\n'
             "  go t v@(DoubleV v') n | even n = rec (n `div` 2)\n"
             '                        | otherwise = right_shift1 : rec ((n-1) `div` 2)\n'
             '   where\n'
             '    right_shift1 = (unit >>> t) &&& iden >>> full_right_shift1 v >>> oh\n'
             "    rec = go (t &&& t) (vectorPromote v')\n"
             '\n'],
            ['Haskell/Core/Simplicity/Programs/Word.hs',
             '\nleft_rotate1 ::',
             '\nrotate_const ::',
             ' (Core term, TyC a, TyC b) => Vector a b -> term b b\n'
             'left_rotate1 v = iden &&& leftmost v >>> full_left_shift1 v >>> ih\n'
             '\n'
             '\n'
             'right_rotate1 :: (Core term, TyC a, TyC b) => Vector a b -> term b b\n'
             'right_rotate1 v = rightmost v &&& iden >>> full_right_shift1 v >>> oh\n'
             '\n'
             '\n'],
            ['Haskell/Core/Simplicity/Programs/Arith.hs',
             '\nfull_subtract ::',
             '\nnegate ::',
             ' (Core term, TyC a) => Word a -> term (Bit, (a, a)) (Bit, a)\n'
             'full_subtract w = not oh &&& drop (oh &&& (ih >>> complement w))\n'
             '              >>> full_add w\n'
             '              >>> not oh &&& ih\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'
             'subtract :: (Core term, TyC a) => Word a -> term (a, a) (Bit, a)\n'
             'subtract w = false &&& iden >>> full_subtract w\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n'
             '\n']],
 'lines': [['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*specificationHash\\ Sha256Block\\s*=([^\\n]*)$',
            'Sha256.hashBlock'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*Sha256Block\\s*::([^\\n]*)$',
            'HashJet (Sha256.Hash, Sha256.Block) Sha256.Hash'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*specificationHash\\ Sha256Ctx8Add1\\s*=([^\\n]*)$',
            'Sha256.ctx8Add1'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*Sha256Ctx8Add1\\s*::([^\\n]*)$',
            'HashJet (Sha256.Ctx8, Word8) Sha256.Ctx8'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*specificationHash\\ Sha256Ctx8Add2\\s*=([^\\n]*)$',
            'Sha256.ctx8Addn vector2'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*Sha256Ctx8Add2\\s*::([^\\n]*)$',
            'HashJet (Sha256.Ctx8, Word16) Sha256.Ctx8'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*specificationHash\\ Sha256Ctx8Add4\\s*=([^\\n]*)$',
            'Sha256.ctx8Addn vector4'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*Sha256Ctx8Add4\\s*::([^\\n]*)$',
            'HashJet (Sha256.Ctx8, Word32) Sha256.Ctx8'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*specificationHash\\ Sha256Ctx8Add8\\s*=([^\\n]*)$',
            'Sha256.ctx8Addn vector8'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*Sha256Ctx8Add8\\s*::([^\\n]*)$',
            'HashJet (Sha256.Ctx8, Word64) Sha256.Ctx8'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*specificationHash\\ Sha256Ctx8Add16\\s*=([^\\n]*)$',
            'Sha256.ctx8Addn vector16'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*Sha256Ctx8Add16\\s*::([^\\n]*)$',
            'HashJet (Sha256.Ctx8, Word128) Sha256.Ctx8'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*specificationHash\\ Sha256Ctx8Add32\\s*=([^\\n]*)$',
            'Sha256.ctx8Addn vector32'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*Sha256Ctx8Add32\\s*::([^\\n]*)$',
            'HashJet (Sha256.Ctx8, Word256) Sha256.Ctx8'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*specificationHash\\ Sha256Ctx8Add64\\s*=([^\\n]*)$',
            'Sha256.ctx8Addn vector64'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*Sha256Ctx8Add64\\s*::([^\\n]*)$',
            'HashJet (Sha256.Ctx8, Word512) Sha256.Ctx8'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*specificationHash\\ Sha256Ctx8Add128\\s*=([^\\n]*)$',
            'Sha256.ctx8Addn vector128'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*Sha256Ctx8Add128\\s*::([^\\n]*)$',
            'HashJet (Sha256.Ctx8, Word1024) Sha256.Ctx8'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*specificationHash\\ Sha256Ctx8Add256\\s*=([^\\n]*)$',
            'Sha256.ctx8Addn vector256'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*Sha256Ctx8Add256\\s*::([^\\n]*)$',
            'HashJet (Sha256.Ctx8, Word2048) Sha256.Ctx8'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*specificationHash\\ Sha256Ctx8Add512\\s*=([^\\n]*)$',
            'Sha256.ctx8Addn vector512'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*Sha256Ctx8Add512\\s*::([^\\n]*)$',
            'HashJet (Sha256.Ctx8, Word4096) Sha256.Ctx8'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*specificationHash\\ Sha256Ctx8AddBuffer511\\s*=([^\\n]*)$',
            'Sha256.ctx8AddBuffer buffer511'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*Sha256Ctx8AddBuffer511\\s*::([^\\n]*)$',
            'HashJet (Sha256.Ctx8, Buffer511 Word8) Sha256.Ctx8'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*specificationHash\\ Sha256Ctx8Finalize\\s*=([^\\n]*)$',
            'Sha256.ctx8Finalize'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*Sha256Ctx8Finalize\\s*::([^\\n]*)$',
            'HashJet Sha256.Ctx8 Sha256.Hash'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*specificationBitcoin\\ TapdataInit\\s*=([^\\n]*)$',
            'Sha256.tapdataInit'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^\\s*TapdataInit\\s*::([^\\n]*)$',
            'BitcoinJet () Sha256.Ctx8'],
           ['Haskell/Simplicity/Bitcoin/Jets.hs',
            '^\\s*specificationSigHash\\ AnnexHash\\s*=([^\\n]*)$',
            'Prog.annexHash'],
           ['Haskell/Simplicity/Bitcoin/Jets.hs',
            '^\\s*AnnexHash\\s*::([^\\n]*)$',
            'SigHashJet (Ctx8, S Word256) Ctx8'],
           ['Haskell/Simplicity/Bitcoin/Jets.hs',
            '^\\s*specificationSigHash\\ OutpointHash\\s*=([^\\n]*)$',
            'Prog.outpointHash'],
           ['Haskell/Simplicity/Bitcoin/Jets.hs',
            '^\\s*OutpointHash\\s*::([^\\n]*)$',
            'SigHashJet (Ctx8, (Word256, Word32)) Ctx8'],
           ['Haskell/Simplicity/Bitcoin/Jets.hs',
            '^\\s*specificationSigHash\\ BuildTapleafSimplicity\\s*=([^\\n]*)$',
            'Prog.buildTapleafSimplicity'],
           ['Haskell/Simplicity/Bitcoin/Jets.hs',
            '^\\s*BuildTapleafSimplicity\\s*::([^\\n]*)$',
            'SigHashJet Word256 Word256'],
           ['Haskell/Simplicity/Bitcoin/Jets.hs',
            '^\\s*specificationSigHash\\ BuildTapbranch\\s*=([^\\n]*)$',
            'Prog.buildTapbranch'],
           ['Haskell/Simplicity/Bitcoin/Jets.hs',
            '^\\s*BuildTapbranch\\s*::([^\\n]*)$',
            'SigHashJet (Word256, Word256) Word256'],
           ['Haskell/Core/Simplicity/Programs/Sha256.hs', '^\\s*libAssert\\s*=([^\\n]*)$', 'mkLibAssert lib'],
           ['Haskell/Core/Simplicity/Programs/Bitcoin.hs', '^\\s*lib\\s*=([^\\n]*)$', 'mkLib Sha256.lib'],
           ['Haskell/Core/Simplicity/Programs/Bitcoin.hs',
            '^\\s*libAssert\\s*=([^\\n]*)$',
            'mkLibAssert Sha256.lib Sha256.libAssert LibSecp256k1.lib'],
           ['Haskell/Core/Simplicity/Programs/Arith.hs', '^\\s*zero\\s*=([^\\n]*)$', 'low'],
           ['Haskell/Core/Simplicity/Programs/Arith.hs',
            '^\\s*one\\ w\\s*=([^\\n]*)$',
            'true >>> left_pad_low word1 w'],
           ['Haskell/Core/Simplicity/Programs/Word.hs', '^\\s*bitwise_maj\\s*=([^\\n]*)$', 'bitwise_tri maj'],
           ['Haskell/Core/Simplicity/Programs/Word.hs', '^\\s*bitwise_ch\\s*=([^\\n]*)$', 'bitwise_tri ch'],
           ['Haskell/Core/Simplicity/Programs/Word.hs',
            '^\\s*bitwise_xor_xor\\s*=([^\\n]*)$',
            'bitwise_tri xor_xor'],
           ['Haskell/Core/Simplicity/Ty/Word.hs', '^\\s*vector1\\s*=([^\\n]*)$', 'SingleV'],
           ['Haskell/Core/Simplicity/Ty/Word.hs', '^\\s*vector2\\s*=([^\\n]*)$', 'DoubleV vector1'],
           ['Haskell/Core/Simplicity/Ty/Word.hs', '^\\s*vector4\\s*=([^\\n]*)$', 'DoubleV vector2'],
           ['Haskell/Core/Simplicity/Ty/Word.hs', '^\\s*vector8\\s*=([^\\n]*)$', 'DoubleV vector4'],
           ['Haskell/Core/Simplicity/Ty/Word.hs', '^\\s*vector16\\s*=([^\\n]*)$', 'DoubleV vector8'],
           ['Haskell/Core/Simplicity/Ty/Word.hs', '^\\s*vector32\\s*=([^\\n]*)$', 'DoubleV vector16'],
           ['Haskell/Core/Simplicity/Ty/Word.hs', '^\\s*vector64\\s*=([^\\n]*)$', 'DoubleV vector32'],
           ['Haskell/Core/Simplicity/Ty/Word.hs', '^\\s*vector128\\s*=([^\\n]*)$', 'DoubleV vector64'],
           ['Haskell/Core/Simplicity/Ty/Word.hs', '^\\s*vector256\\s*=([^\\n]*)$', 'DoubleV vector128'],
           ['Haskell/Core/Simplicity/Ty/Word.hs', '^\\s*vector512\\s*=([^\\n]*)$', 'DoubleV vector256'],
           ['Haskell/Core/Simplicity/Ty/Word.hs', '^\\s*word1\\s*=([^\\n]*)$', 'vector1'],
           ['Haskell/Core/Simplicity/Ty/Word.hs', '^\\s*word8\\s*=([^\\n]*)$', 'vector8'],
           ['Haskell/Core/Simplicity/Ty/Word.hs', '^\\s*word16\\s*=([^\\n]*)$', 'vector16'],
           ['Haskell/Core/Simplicity/Ty/Word.hs', '^\\s*word32\\s*=([^\\n]*)$', 'vector32'],
           ['Haskell/Core/Simplicity/Ty/Word.hs', '^\\s*word64\\s*=([^\\n]*)$', 'vector64'],
           ['Haskell/Core/Simplicity/Ty/Word.hs', '^\\s*word128\\s*=([^\\n]*)$', 'vector128'],
           ['Haskell/Core/Simplicity/Ty/Word.hs', '^\\s*word256\\s*=([^\\n]*)$', 'vector256'],
           ['Haskell/Core/Simplicity/Ty/Word.hs', '^\\s*word512\\s*=([^\\n]*)$', 'vector512'],
           ['Haskell/Core/Simplicity/Ty/Word.hs', '^\\s*word1024\\s*=([^\\n]*)$', 'vector1024'],
           ['Haskell/Core/Simplicity/Ty/Word.hs', '^\\s*word2048\\s*=([^\\n]*)$', 'vector2048'],
           ['Haskell/Core/Simplicity/Ty/Word.hs', '^\\s*word4096\\s*=([^\\n]*)$', 'vector4096'],
           ['Haskell/Core/Simplicity/Programs/Sha256.hs', '^type Block\\s*=([^\\n]*)$', 'Word512'],
           ['Haskell/Core/Simplicity/Programs/Sha256.hs', '^type Hash\\s*=([^\\n]*)$', 'Word256'],
           ['Haskell/Core/Simplicity/Programs/Sha256.hs',
            '^type Ctx8\\s*=([^\\n]*)$',
            '(Buffer63 Word8, (Word64, Word256))'],
           ['Haskell/Core/Simplicity/Programs/Bit.hs', '^\\s*false\\s*=([^\\n]*)$', 'injl unit'],
           ['Haskell/Core/Simplicity/Programs/Bit.hs', '^\\s*true\\s*=([^\\n]*)$', 'injr unit'],
           ['Haskell/Core/Simplicity/Programs/Bit.hs',
            '^\\s*maj\\s*=([^\\n]*)$',
            'cond (cond true iden) (cond iden false)'],
           ['Haskell/Core/Simplicity/Programs/Arith.hs', '^\\s*lt\\ w\\s*=([^\\n]*)$', 'subtract w >>> oh'],
           ['Haskell/Core/Simplicity/CoreJets.hs',
            '^import\\ qualified\\ Simplicity\\.Programs\\.Sha256\\.Lib\\ as\\ Sha256$',
            'import qualified Simplicity.Programs.Sha256.Lib as Sha256'],
           ['Haskell/Simplicity/Bitcoin/Jets.hs',
            '^import\\ qualified\\ Simplicity\\.Programs\\.Bitcoin\\.Lib\\ as\\ Prog$',
            'import qualified Simplicity.Programs.Bitcoin.Lib as Prog']],
 'files': [['Haskell/Core/Simplicity/Programs/Sha256/Lib.hs',
            ' \n'
            '\n'
            '\n'
            '\n'
            'module Simplicity.Programs.Sha256.Lib\n'
            ' (\n'
            ' \n'
            '   Sha256.Block, Sha256.Hash, Sha256.Ctx8\n'
            ' , iv, hashBlock\n'
            ' , ctx8Init\n'
            ' , tapdataInit\n'
            ' , ctx8Add1\n'
            ' , ctx8Addn\n'
            ' , ctx8AddBuffer\n'
            ' , ctx8Add2\n'
            ' , ctx8Add4\n'
            ' , ctx8Add8\n'
            ' , ctx8Add16\n'
            ' , ctx8Add32\n'
            ' , ctx8Add64\n'
            ' , ctx8Add128\n'
            ' , ctx8Add256\n'
            ' , ctx8Add512\n'
            ' , ctx8AddBuffer511\n'
            ' , ctx8Finalize\n'
            ' , hashLoop\n'
            ' , ctx8InitTag\n'
            ' ) where\n'
            '\n'
            'import qualified Simplicity.Programs.Sha256 as Sha256\n'
            'import Simplicity.Ty.Word\n'
            '\n'
            'iv = Sha256.iv Sha256.lib\n'
            'hashBlock = Sha256.hashBlock Sha256.lib\n'
            'ctx8Init = Sha256.ctx8Init Sha256.lib\n'
            'tapdataInit = Sha256.tapdataInit Sha256.lib\n'
            'ctx8Add1 = Sha256.ctx8Add1 Sha256.libAssert\n'
            'ctx8Addn = Sha256.ctx8Addn Sha256.libAssert\n'
            'ctx8AddBuffer = Sha256.ctx8AddBuffer Sha256.libAssert\n'
            'ctx8Add2 = ctx8Addn vector2\n'
            'ctx8Add4 = ctx8Addn vector4\n'
            'ctx8Add8 = ctx8Addn vector8\n'
            'ctx8Add16 = ctx8Addn vector16\n'
            'ctx8Add32 = ctx8Addn vector32\n'
            'ctx8Add64 = ctx8Addn vector64\n'
            'ctx8Add128 = ctx8Addn vector128\n'
            'ctx8Add256 = ctx8Addn vector256\n'
            'ctx8Add512 = ctx8Addn vector512\n'
            'ctx8AddBuffer511 = ctx8AddBuffer buffer511\n'
            'ctx8Finalize = Sha256.ctx8Finalize Sha256.libAssert\n'
            'hashLoop = Sha256.hashLoop\n'
            'ctx8InitTag = Sha256.ctx8InitTag\n'],
           ['Haskell/Core/Simplicity/Programs/Bitcoin/Lib.hs',
            ' \n'
            '\n'
            '\n'
            '\n'
            'module Simplicity.Programs.Bitcoin.Lib\n'
            '  ( buildTapleafSimplicity, buildTapbranch\n'
            '  , outpointHash, annexHash\n'
            '  , buildTaptweak\n'
            '  , Bitcoin.Hash, Bitcoin.Ctx8\n'
            '  ) where\n'
            '\n'
            'import qualified Simplicity.Programs.Bitcoin as Bitcoin\n'
            '\n'
            '\n'
            'buildTapleafSimplicity = Bitcoin.buildTapleafSimplicity Bitcoin.lib\n'
            'buildTapbranch = Bitcoin.buildTapbranch Bitcoin.lib\n'
            'outpointHash = Bitcoin.outpointHash Bitcoin.libAssert\n'
            'annexHash = Bitcoin.annexHash Bitcoin.libAssert\n'
            'buildTaptweak = Bitcoin.buildTaptweak Bitcoin.libAssert\n'],
           ['Haskell/Core/Simplicity/Ty/Word.hs',
            ' \n'
            '\n'
            '\n'
            'module Simplicity.Ty.Word\n'
            '  ( Vector(..), vectorComp, vectorPromote, compareVectorSize\n'
            '  , vectorSize, vector_\n'
            '  , Buffer(..), bufferFill, bufferVector, buffer_\n'
            '  , Word, wordSize, fromWord, toWord\n'
            '  \n'
            '  \n'
            '  \n'
            '  , Word1, Word2, Word4, Word8, Word16, Word32, Word64, Word128, Word256, Word512, Word1024, '
            'Word2048, Word4096\n'
            '  , Vector1, Vector2, Vector4, Vector8, Vector16, Vector32, Vector64, Vector128, Vector256, '
            'Vector512, Vector1024, Vector2048, Vector4096\n'
            '  , vector1, vector2, vector4, vector8, vector16, vector32, vector64, vector128, vector256, '
            'vector512, vector1024, vector2048, vector4096\n'
            '  , Buffer1, Buffer3, Buffer7, Buffer15, Buffer31, Buffer63, Buffer127, Buffer255, Buffer511\n'
            '  , buffer1, buffer3, buffer7, buffer15, buffer31, buffer63, buffer127, buffer255, buffer511\n'
            '  \n'
            '  \n'
            '  \n'
            '\n'
            '  \n'
            '  , word1, fromWord1, fromInt1, toWord1\n'
            '  \n'
            '  , word2, fromWord2, fromInt2, toWord2\n'
            '  \n'
            '  , word4, fromWord4, fromInt4, toWord4\n'
            '  \n'
            '  , word8, fromWord8, fromInt8, toWord8\n'
            '  \n'
            '  , word16, fromWord16, fromInt16, toWord16\n'
            '  \n'
            '  , word32, fromWord32, fromInt32, toWord32\n'
            '  \n'
            '  , word64, fromWord64, fromInt64, toWord64\n'
            '  \n'
            '  , word128, fromWord128, fromInt128, toWord128\n'
            '  \n'
            '  , word256, fromWord256, fromInt256, toWord256\n'
            '  \n'
            '  , word512, fromWord512, fromInt512, toWord512\n'
            '  \n'
            '  , word1024, fromWord1024, fromInt1024, toWord1024\n'
            '  \n'
            '  , word2048, fromWord2048, fromInt2048, toWord2048\n'
            '  \n'
            '  , word4096, fromWord4096, fromInt4096, toWord4096\n'
            '  \n'
            '  , ZipVector(..)\n'
            '  \n'
            '  , module Simplicity.Ty.Bit\n'
            '  ) where\n'
            '\n'
            'import Prelude hiding (Word)\n'
            '\n'
            'import Control.Monad.Trans.State (State, evalState, get, put)\n'
            'import Data.Type.Equality ((:~:)(Refl))\n'
            "import Lens.Family2.Stock (Traversal', rgt_)\n"
            '\n'
            'import Simplicity.Ty\n'
            'import Simplicity.Ty.Bit\n'
            '\n'
            'right_ f = rgt_ f\n'
            '\n'
            'type Vector1 x = x\n'
            'type Vector2 x = (x,x)\n'
            'type Vector4 x = Vector2 (Vector2 x)\n'
            'type Vector8 x = Vector2 (Vector4 x)\n'
            'type Vector16 x = Vector2 (Vector8 x)\n'
            'type Vector32 x = Vector2 (Vector16 x)\n'
            'type Vector64 x = Vector2 (Vector32 x)\n'
            'type Vector128 x = Vector2 (Vector64 x)\n'
            'type Vector256 x = Vector2 (Vector128 x)\n'
            'type Vector512 x = Vector2 (Vector256 x)\n'
            'type Vector1024 x = Vector2 (Vector512 x)\n'
            'type Vector2048 x = Vector2 (Vector1024 x)\n'
            'type Vector4096 x = Vector2 (Vector2048 x)\n'
            '\n'
            'vector1 :: TyC x => Vector x (Vector1 x)\n'
            'vector1 = SingleV\n'
            '\n'
            'vector2 :: TyC x => Vector x (Vector2 x)\n'
            'vector2 = DoubleV vector1\n'
            '\n'
            'vector4 :: TyC x => Vector x (Vector4 x)\n'
            'vector4 = DoubleV vector2\n'
            '\n'
            'vector8 :: TyC x => Vector x (Vector8 x)\n'
            'vector8 = DoubleV vector4\n'
            '\n'
            'vector16 :: TyC x => Vector x (Vector16 x)\n'
            'vector16 = DoubleV vector8\n'
            '\n'
            'vector32 :: TyC x => Vector x (Vector32 x)\n'
            'vector32 = DoubleV vector16\n'
            '\n'
            'vector64 :: TyC x => Vector x (Vector64 x)\n'
            'vector64 = DoubleV vector32\n'
            '\n'
            'vector128 :: TyC x => Vector x (Vector128 x)\n'
            'vector128 = DoubleV vector64\n'
            '\n'
            'vector256 :: TyC x => Vector x (Vector256 x)\n'
            'vector256 = DoubleV vector128\n'
            '\n'
            'vector512 :: TyC x => Vector x (Vector512 x)\n'
            'vector512 = DoubleV vector256\n'
            '\n'
            'vector1024 :: TyC x => Vector x (Vector1024 x)\n'
            'vector1024 = DoubleV vector512\n'
            '\n'
            'vector2048 :: TyC x => Vector x (Vector2048 x)\n'
            'vector2048 = DoubleV vector1024\n'
            '\n'
            'vector4096 :: TyC x => Vector x (Vector4096 x)\n'
            'vector4096 = DoubleV vector2048\n'
            '\n'
            '\n'
            '\n'
            '\n'
            'data Vector x a where\n'
            '  SingleV :: TyC x => Vector x x\n'
            '  DoubleV :: (TyC x, TyC a) => Vector x a -> Vector x (Vector2 a)\n'
            '\n'
            '\n'
            'vectorComp :: TyC a => Vector a b -> Vector b c -> Vector a c\n'
            'vectorComp v SingleV = v\n'
            'vectorComp v (DoubleV w) = DoubleV (vectorComp v w)\n'
            '\n'
            '\n'
            'vectorPromote :: Vector x y -> Vector (x, x) (y, y)\n'
            'vectorPromote SingleV = SingleV\n'
            'vectorPromote (DoubleV v) = DoubleV (vectorPromote v)\n'
            '\n'
            '\n'
            'compareVectorSize :: Vector z a -> Vector z b -> Either (Vector (b, b) a) (Either (a :~: b) '
            '(Vector (a, a) b))\n'
            'compareVectorSize SingleV SingleV = Right (Left Refl)\n'
            'compareVectorSize (DoubleV n) SingleV =\n'
            '  case compareVectorSize n SingleV of\n'
            '    Left v -> Left (DoubleV v)\n'
            '    Right (Left Refl) -> Left SingleV\n'
            'compareVectorSize SingleV (DoubleV m) =\n'
            '  case compareVectorSize SingleV m of\n'
            '    Right (Left Refl) -> Right (Right SingleV)\n'
            '    Right (Right v) -> Right (Right (DoubleV v))\n'
            'compareVectorSize (DoubleV n) (DoubleV m) =\n'
            '  case compareVectorSize n m of\n'
            '    Left v -> Left (vectorPromote v)\n'
            '    Right (Left Refl) -> Right (Left Refl)\n'
            '    Right (Right v) -> Right (Right (vectorPromote v))\n'
            '\n'
            '\n'
            '\n'
            '\n'
            'vectorFill :: Vector x a -> [x] -> Maybe (a, [x])\n'
            'vectorFill SingleV [] = Nothing\n'
            'vectorFill SingleV (x:xs) = Just (x, xs)\n'
            'vectorFill (DoubleV vec) l = do\n'
            "  (v1, l') <- vectorFill vec l\n"
            "  (v2, l'') <- vectorFill vec l'\n"
            "  return ((v1,v2),l'')\n"
            '\n'
            '\n'
            'vectorSize :: Vector x a -> Int\n'
            'vectorSize SingleV = 1\n'
            'vectorSize (DoubleV w) = 2*(vectorSize w)\n'
            '\n'
            '\n'
            "vector_ :: Vector x a -> Traversal' a x\n"
            'vector_ SingleV = ($)\n'
            'vector_ (DoubleV v) = \\f (x,y) -> (,) <$> rec f x <*> rec f y\n'
            ' where\n'
            '  rec = vector_ v\n'
            '\n'
            'type Buffer1 x = S x\n'
            'type Buffer3 x = (S (Vector2 x), Buffer1 x)\n'
            'type Buffer7 x = (S (Vector4 x), Buffer3 x)\n'
            'type Buffer15 x = (S (Vector8 x), Buffer7 x)\n'
            'type Buffer31 x = (S (Vector16 x), Buffer15 x)\n'
            'type Buffer63 x = (S (Vector32 x), Buffer31 x)\n'
            'type Buffer127 x = (S (Vector64 x), Buffer63 x)\n'
            'type Buffer255 x = (S (Vector128 x), Buffer127 x)\n'
            'type Buffer511 x = (S (Vector256 x), Buffer255 x)\n'
            '\n'
            '\n'
            '\n'
            '\n'
            '\n'
            '\n'
            '\n'
            '\n'
            '\n'
            'data Buffer x v b where\n'
            ' SingleB :: TyC x => Buffer x (Vector2 x) (S x)\n'
            ' DoubleB :: (TyC x, TyC v, TyC b) => Buffer x v b -> Buffer x (Vector2 v) (S v, b)\n'
            '\n'
            'buffer1 :: TyC x => Buffer x (Vector2 x) (Buffer1 x)\n'
            'buffer1 = SingleB\n'
            '\n'
            'buffer3 :: TyC x => Buffer x (Vector4 x) (Buffer3 x)\n'
            'buffer3 = DoubleB buffer1\n'
            '\n'
            'buffer7 :: TyC x => Buffer x (Vector8 x) (Buffer7 x)\n'
            'buffer7 = DoubleB buffer3\n'
            '\n'
            'buffer15 :: TyC x => Buffer x (Vector16 x) (Buffer15 x)\n'
            'buffer15 = DoubleB buffer7\n'
            '\n'
            'buffer31 :: TyC x => Buffer x (Vector32 x) (Buffer31 x)\n'
            'buffer31 = DoubleB buffer15\n'
            '\n'
            'buffer63 :: TyC x => Buffer x (Vector64 x) (Buffer63 x)\n'
            'buffer63 = DoubleB buffer31\n'
            '\n'
            'buffer127 :: TyC x => Buffer x (Vector128 x) (Buffer127 x)\n'
            'buffer127 = DoubleB buffer63\n'
            '\n'
            'buffer255 :: TyC x => Buffer x (Vector256 x) (Buffer255 x)\n'
            'buffer255 = DoubleB buffer127\n'
            '\n'
            'buffer511 :: TyC x => Buffer x (Vector512 x) (Buffer511 x)\n'
            'buffer511 = DoubleB buffer255\n'
            '\n'
            '\n'
            'bufferVector  :: Buffer x v b -> Vector x v\n'
            'bufferVector SingleB = vector2\n'
            'bufferVector (DoubleB buf) = DoubleV (bufferVector buf)\n'
            '\n'
            '\n'
            'bufferEmpty :: Buffer x v b -> b\n'
            'bufferEmpty SingleB = Left ()\n'
            'bufferEmpty (DoubleB buf) = (Left (), bufferEmpty buf)\n'
            '\n'
            '\n'
            'bufferFill :: Buffer x v b -> [x] -> (b,[x])\n'
            'bufferFill buf [] = (bufferEmpty buf, [])\n'
            'bufferFill SingleB (x:xs) = (Right x, xs)\n'
            'bufferFill (DoubleB buf) l = case vectorFill (bufferVector buf) l of\n'
            "  Nothing -> let (rec,l'') = bufferFill buf l in ((Left (), rec), l'')\n"
            "  Just (v, l') -> let (rec, l'') = bufferFill buf l' in ((Right v, rec), l'')\n"
            '\n'
            '\n'
            "buffer_ :: Buffer x v b -> Traversal' b x\n"
            'buffer_ SingleB = right_\n'
            'buffer_ (DoubleB v) = \\f (x,y) -> (,) <$> (right_.vector_ (bufferVector v)) f x  <*> buffer_ v '
            'f y\n'
            '\n'
            'type Word1 = Vector1 Bit\n'
            'type Word2 = Vector2 Bit\n'
            'type Word4 = Vector4 Bit\n'
            'type Word8 = Vector8 Bit\n'
            'type Word16 = Vector16 Bit\n'
            'type Word32 = Vector32 Bit\n'
            'type Word64 = Vector64 Bit\n'
            'type Word128 = Vector128 Bit\n'
            'type Word256 = Vector256 Bit\n'
            'type Word512 = Vector512 Bit\n'
            'type Word1024 = Vector1024 Bit\n'
            'type Word2048 = Vector2048 Bit\n'
            'type Word4096 = Vector4096 Bit\n'
            '\n'
            '\n'
            '\n'
            '\n'
            'type Word = Vector Bit\n'
            '\n'
            'word1 :: Word Word1\n'
            'word1 = vector1\n'
            '\n'
            'word2 :: Word Word2\n'
            'word2 = vector2\n'
            '\n'
            'word4 :: Word Word4\n'
            'word4 = vector4\n'
            '\n'
            'word8 :: Word Word8\n'
            'word8 = vector8\n'
            '\n'
            'word16 :: Word Word16\n'
            'word16 = vector16\n'
            '\n'
            'word32 :: Word Word32\n'
            'word32 = vector32\n'
            '\n'
            'word64 :: Word Word64\n'
            'word64 = vector64\n'
            '\n'
            'word128 :: Word Word128\n'
            'word128 = vector128\n'
            '\n'
            'word256 :: Word Word256\n'
            'word256 = vector256\n'
            '\n'
            'word512 :: Word Word512\n'
            'word512 = vector512\n'
            '\n'
            'word1024 :: Word Word1024\n'
            'word1024 = vector1024\n'
            '\n'
            'word2048 :: Word Word2048\n'
            'word2048 = vector2048\n'
            '\n'
            'word4096 :: Word Word4096\n'
            'word4096 = vector4096\n'
            '\n'
            '\n'
            '\n'
            '\n'
            'wordSize :: Word a -> Int\n'
            'wordSize = vectorSize\n'
            '\n'
            '\n'
            '\n'
            '\n'
            'fromWord :: Word a -> a -> Integer\n'
            'fromWord = fromWordRec 0\n'
            '\n'
            'fromWordRec :: Integer -> Word a -> a -> Integer\n'
            'fromWordRec i SingleV (Left ()) = 2 * i\n'
            'fromWordRec i SingleV (Right ()) = 2 * i + 1\n'
            'fromWordRec i (DoubleV w) (hi, lo) = fromWordRec (fromWordRec i w hi) w lo\n'
            '\n'
            '\n'
            '\n'
            '\n'
            'fromInt :: Word a -> a -> Integer\n'
            'fromInt SingleV (Left ()) = 0\n'
            'fromInt SingleV (Right ()) = -1\n'
            'fromInt (DoubleV w) (hi, lo) = fromWordRec (fromInt w hi) w lo\n'
            '\n'
            '\n'
            '\n'
            '\n'
            '\n'
            'toWord :: Word a -> Integer -> a\n'
            'toWord w i = evalState (go w) i\n'
            ' where\n'
            '  go :: Word a -> State Integer a\n'
            '  go SingleV = do\n'
            '   i <- get\n'
            '   put (i `div` 2)\n'
            '   return $ toBit (odd i)\n'
            '  go (DoubleV w) = do\n'
            '   b <- go w\n'
            '   a <- go w\n'
            '   return (a, b)\n'
            '\n'
            'fromWord1 :: Word1 -> Integer\n'
            'fromWord1 = fromWord word1\n'
            '\n'
            'fromWord2 :: Word2 -> Integer\n'
            'fromWord2 = fromWord word2\n'
            '\n'
            'fromWord4 :: Word4 -> Integer\n'
            'fromWord4 = fromWord word4\n'
            '\n'
            'fromWord8 :: Word8 -> Integer\n'
            'fromWord8 = fromWord word8\n'
            '\n'
            'fromWord16 :: Word16 -> Integer\n'
            'fromWord16 = fromWord word16\n'
            '\n'
            'fromWord32 :: Word32 -> Integer\n'
            'fromWord32 = fromWord word32\n'
            '\n'
            'fromWord64 :: Word64 -> Integer\n'
            'fromWord64 = fromWord word64\n'
            '\n'
            'fromWord128 :: Word128 -> Integer\n'
            'fromWord128 = fromWord word128\n'
            '\n'
            'fromWord256 :: Word256 -> Integer\n'
            'fromWord256 = fromWord word256\n'
            '\n'
            'fromWord512 :: Word512 -> Integer\n'
            'fromWord512 = fromWord word512\n'
            '\n'
            'fromWord1024 :: Word1024 -> Integer\n'
            'fromWord1024 = fromWord word1024\n'
            '\n'
            'fromWord2048 :: Word2048 -> Integer\n'
            'fromWord2048 = fromWord word2048\n'
            '\n'
            'fromWord4096 :: Word4096 -> Integer\n'
            'fromWord4096 = fromWord word4096\n'
            '\n'
            'fromInt1 :: Word1 -> Integer\n'
            'fromInt1 = fromInt word1\n'
            '\n'
            'fromInt2 :: Word2 -> Integer\n'
            'fromInt2 = fromInt word2\n'
            '\n'
            'fromInt4 :: Word4 -> Integer\n'
            'fromInt4 = fromInt word4\n'
            '\n'
            'fromInt8 :: Word8 -> Integer\n'
            'fromInt8 = fromInt word8\n'
            '\n'
            'fromInt16 :: Word16 -> Integer\n'
            'fromInt16 = fromInt word16\n'
            '\n'
            'fromInt32 :: Word32 -> Integer\n'
            'fromInt32 = fromInt word32\n'
            '\n'
            'fromInt64 :: Word64 -> Integer\n'
            'fromInt64 = fromInt word64\n'
            '\n'
            'fromInt128 :: Word128 -> Integer\n'
            'fromInt128 = fromInt word128\n'
            '\n'
            'fromInt256 :: Word256 -> Integer\n'
            'fromInt256 = fromInt word256\n'
            '\n'
            'fromInt512 :: Word512 -> Integer\n'
            'fromInt512 = fromInt word512\n'
            '\n'
            'fromInt1024 :: Word1024 -> Integer\n'
            'fromInt1024 = fromInt word1024\n'
            '\n'
            'fromInt2048 :: Word2048 -> Integer\n'
            'fromInt2048 = fromInt word2048\n'
            '\n'
            'fromInt4096 :: Word4096 -> Integer\n'
            'fromInt4096 = fromInt word4096\n'
            '\n'
            'toWord1 :: Integer -> Word1\n'
            'toWord1 = toWord word1\n'
            '\n'
            'toWord2 :: Integer -> Word2\n'
            'toWord2 = toWord word2\n'
            '\n'
            'toWord4 :: Integer -> Word4\n'
            'toWord4 = toWord word4\n'
            '\n'
            'toWord8 :: Integer -> Word8\n'
            'toWord8 = toWord word8\n'
            '\n'
            'toWord16 :: Integer -> Word16\n'
            'toWord16 = toWord word16\n'
            '\n'
            'toWord32 :: Integer -> Word32\n'
            'toWord32 = toWord word32\n'
            '\n'
            'toWord64 :: Integer -> Word64\n'
            'toWord64 = toWord word64\n'
            '\n'
            'toWord128 :: Integer -> Word128\n'
            'toWord128 = toWord word128\n'
            '\n'
            'toWord256 :: Integer -> Word256\n'
            'toWord256 = toWord word256\n'
            '\n'
            'toWord512 :: Integer -> Word512\n'
            'toWord512 = toWord word512\n'
            '\n'
            'toWord1024 :: Integer -> Word1024\n'
            'toWord1024 = toWord word1024\n'
            '\n'
            'toWord2048 :: Integer -> Word2048\n'
            'toWord2048 = toWord word2048\n'
            '\n'
            'toWord4096 :: Integer -> Word4096\n'
            'toWord4096 = toWord word4096\n'
            '\n'
            '\n'
            'data ZipVector x a y b where\n'
            '  SingleZV :: (TyC x, TyC y) => ZipVector x x y y\n'
            '  DoubleZV :: (TyC x, TyC a, TyC y, TyC b) => ZipVector x a y b -> ZipVector x (Vector2 a) y '
            '(Vector2 b)\n']],
 'c_functions': [['C/jets.c',
                  'simplicity_sha_256_block',
                  'bool simplicity_sha_256_block(frameItem* dst, frameItem src, const txEnv* env) {\n'
                  '  (void) env;  \n'
                  '  uint32_t h[8];\n'
                  '  uint32_t block[16];\n'
                  '  read32s(h, 8, &src);\n'
                  '  read32s(block, 16, &src);\n'
                  '  simplicity_sha256_compression(h, block);\n'
                  '  write32s(dst, h, 8);\n'
                  '  return true;\n'
                  '}'],
                 ['C/jets.c',
                  'simplicity_sha_256_ctx_8_add_1',
                  'bool simplicity_sha_256_ctx_8_add_1(frameItem* dst, frameItem src, const txEnv* env) {\n'
                  '  (void) env;  \n'
                  '  return sha_256_ctx_8_add_n(dst, &src, 1);\n'
                  '}'],
                 ['C/jets.c',
                  'simplicity_sha_256_ctx_8_add_2',
                  'bool simplicity_sha_256_ctx_8_add_2(frameItem* dst, frameItem src, const txEnv* env) {\n'
                  '  (void) env;  \n'
                  '  return sha_256_ctx_8_add_n(dst, &src, 2);\n'
                  '}'],
                 ['C/jets.c',
                  'simplicity_sha_256_ctx_8_add_4',
                  'bool simplicity_sha_256_ctx_8_add_4(frameItem* dst, frameItem src, const txEnv* env) {\n'
                  '  (void) env;  \n'
                  '  return sha_256_ctx_8_add_n(dst, &src, 4);\n'
                  '}'],
                 ['C/jets.c',
                  'simplicity_sha_256_ctx_8_add_8',
                  'bool simplicity_sha_256_ctx_8_add_8(frameItem* dst, frameItem src, const txEnv* env) {\n'
                  '  (void) env;  \n'
                  '  return sha_256_ctx_8_add_n(dst, &src, 8);\n'
                  '}'],
                 ['C/jets.c',
                  'simplicity_sha_256_ctx_8_add_16',
                  'bool simplicity_sha_256_ctx_8_add_16(frameItem* dst, frameItem src, const txEnv* env) {\n'
                  '  (void) env;  \n'
                  '  return sha_256_ctx_8_add_n(dst, &src, 16);\n'
                  '}'],
                 ['C/jets.c',
                  'simplicity_sha_256_ctx_8_add_32',
                  'bool simplicity_sha_256_ctx_8_add_32(frameItem* dst, frameItem src, const txEnv* env) {\n'
                  '  (void) env;  \n'
                  '  return sha_256_ctx_8_add_n(dst, &src, 32);\n'
                  '}'],
                 ['C/jets.c',
                  'simplicity_sha_256_ctx_8_add_64',
                  'bool simplicity_sha_256_ctx_8_add_64(frameItem* dst, frameItem src, const txEnv* env) {\n'
                  '  (void) env;  \n'
                  '  return sha_256_ctx_8_add_n(dst, &src, 64);\n'
                  '}'],
                 ['C/jets.c',
                  'simplicity_sha_256_ctx_8_add_128',
                  'bool simplicity_sha_256_ctx_8_add_128(frameItem* dst, frameItem src, const txEnv* env) {\n'
                  '  (void) env;  \n'
                  '  return sha_256_ctx_8_add_n(dst, &src, 128);\n'
                  '}'],
                 ['C/jets.c',
                  'simplicity_sha_256_ctx_8_add_256',
                  'bool simplicity_sha_256_ctx_8_add_256(frameItem* dst, frameItem src, const txEnv* env) {\n'
                  '  (void) env;  \n'
                  '  return sha_256_ctx_8_add_n(dst, &src, 256);\n'
                  '}'],
                 ['C/jets.c',
                  'simplicity_sha_256_ctx_8_add_512',
                  'bool simplicity_sha_256_ctx_8_add_512(frameItem* dst, frameItem src, const txEnv* env) {\n'
                  '  (void) env;  \n'
                  '  return sha_256_ctx_8_add_n(dst, &src, 512);\n'
                  '}'],
                 ['C/jets.c',
                  'simplicity_sha_256_ctx_8_add_buffer_511',
                  'bool simplicity_sha_256_ctx_8_add_buffer_511(frameItem* dst, frameItem src, const txEnv* '
                  'env) {\n'
                  '  (void) env;  \n'
                  '  sha256_midstate midstate;\n'
                  '  unsigned char buf[511];\n'
                  '  size_t buf_len;\n'
                  '  sha256_context ctx = {.output = midstate.s};\n'
                  '\n'
                  '  if (!simplicity_read_sha256_context(&ctx, &src)) return false;\n'
                  '\n'
                  '  simplicity_read_buffer8(buf, &buf_len, &src, 8);\n'
                  '  sha256_uchars(&ctx, buf, buf_len);\n'
                  '  return simplicity_write_sha256_context(dst, &ctx);\n'
                  '}'],
                 ['C/jets.c',
                  'simplicity_sha_256_ctx_8_finalize',
                  'bool simplicity_sha_256_ctx_8_finalize(frameItem* dst, frameItem src, const txEnv* env) '
                  '{\n'
                  '  (void) env;  \n'
                  '  sha256_midstate midstate;\n'
                  '  sha256_context ctx = {.output = midstate.s};\n'
                  '\n'
                  '  if (!simplicity_read_sha256_context(&ctx, &src)) return false;\n'
                  '\n'
                  '  sha256_finalize(&ctx);\n'
                  '  write32s(dst, midstate.s, 8);\n'
                  '  return true;\n'
                  '}'],
                 ['C/jets.c',
                  'simplicity_tapdata_init',
                  'bool simplicity_tapdata_init(frameItem* dst, frameItem src, const txEnv* env) {\n'
                  '  (void) env;  \n'
                  '  (void) src;  \n'
                  '\n'
                  '  sha256_midstate tapleafTag;\n'
                  '  {\n'
                  '    static const unsigned char tagName[] = "TapData";\n'
                  '    sha256_context ctx = sha256_init(tapleafTag.s);\n'
                  '    sha256_uchars(&ctx, tagName, sizeof(tagName) - 1);\n'
                  '    sha256_finalize(&ctx);\n'
                  '  }\n'
                  '  uint32_t iv[8];\n'
                  '  sha256_context ctx = sha256_init(iv);\n'
                  '  sha256_hash(&ctx, &tapleafTag);\n'
                  '  sha256_hash(&ctx, &tapleafTag);\n'
                  '\n'
                  '  return simplicity_write_sha256_context(dst, &ctx);\n'
                  '}'],
                 ['C/jets.c',
                  'sha_256_ctx_8_add_n',
                  'static bool sha_256_ctx_8_add_n(frameItem* dst, frameItem *src, size_t n) {\n'
                  '  simplicity_debug_assert(0 < n && n <= 512 && (n & (n - 1)) == 0);\n'
                  '  sha256_midstate midstate;\n'
                  '  unsigned char buf[512];\n'
                  '  sha256_context ctx = {.output = midstate.s};\n'
                  '\n'
                  '  if (!simplicity_read_sha256_context(&ctx, src)) return false;\n'
                  '  read8s(buf, n, src);\n'
                  '  sha256_uchars(&ctx, buf, n);\n'
                  '  return simplicity_write_sha256_context(dst, &ctx);\n'
                  '}'],
                 ['C/bitcoin/bitcoinJets.c',
                  'simplicity_bitcoin_annex_hash',
                  'bool simplicity_bitcoin_annex_hash(frameItem* dst, frameItem src, const txEnv* env) {\n'
                  '  (void) env;  \n'
                  '  sha256_midstate midstate;\n'
                  '  unsigned char buf[32];\n'
                  '  sha256_context ctx = {.output = midstate.s};\n'
                  '\n'
                  '   \n'
                  '  if (!simplicity_read_sha256_context(&ctx, &src)) return false;\n'
                  '\n'
                  '   \n'
                  '  if (readBit(&src)) {\n'
                  '     \n'
                  '    read8s(buf, 32, &src);\n'
                  '    sha256_uchar(&ctx, 0x01);\n'
                  '    sha256_uchars(&ctx, buf, 32);\n'
                  '  } else {\n'
                  '     \n'
                  '    sha256_uchar(&ctx, 0x00);\n'
                  '  }\n'
                  '\n'
                  '  return simplicity_write_sha256_context(dst, &ctx);\n'
                  '}'],
                 ['C/bitcoin/bitcoinJets.c',
                  'simplicity_bitcoin_outpoint_hash',
                  'bool simplicity_bitcoin_outpoint_hash(frameItem* dst, frameItem src, const txEnv* env) {\n'
                  '  (void) env;  \n'
                  '  sha256_midstate midstate;\n'
                  '  unsigned char buf[36];\n'
                  '  sha256_context ctx = {.output = midstate.s};\n'
                  '\n'
                  '   \n'
                  '  if (!simplicity_read_sha256_context(&ctx, &src)) return false;\n'
                  '\n'
                  '   \n'
                  '  read8s(buf, 36, &src);\n'
                  '  sha256_uchars(&ctx, buf, 36);\n'
                  '\n'
                  '  return simplicity_write_sha256_context(dst, &ctx);\n'
                  '}'],
                 ['C/bitcoin/bitcoinJets.c',
                  'simplicity_bitcoin_build_tapleaf_simplicity',
                  'bool simplicity_bitcoin_build_tapleaf_simplicity(frameItem* dst, frameItem src, const '
                  'txEnv* env) {\n'
                  '  (void) env;  \n'
                  '  sha256_midstate cmr;\n'
                  '  readHash(&cmr, &src);\n'
                  '  sha256_midstate result = simplicity_bitcoin_make_tapleaf(0xbe, &cmr);\n'
                  '  writeHash(dst, &result);\n'
                  '  return true;\n'
                  '}'],
                 ['C/bitcoin/bitcoinJets.c',
                  'simplicity_bitcoin_build_tapbranch',
                  'bool simplicity_bitcoin_build_tapbranch(frameItem* dst, frameItem src, const txEnv* env) '
                  '{\n'
                  '  (void) env;  \n'
                  '  sha256_midstate a, b;\n'
                  '  readHash(&a, &src);\n'
                  '  readHash(&b, &src);\n'
                  '\n'
                  '  sha256_midstate result = simplicity_bitcoin_make_tapbranch(&a, &b);\n'
                  '  writeHash(dst, &result);\n'
                  '  return true;\n'
                  '}']]}
