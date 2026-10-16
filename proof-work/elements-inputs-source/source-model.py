"""Fixed reviewed Elements inputsHash composition/source model."""
MODEL = {'declarations': [['Coq/C/jet_elements_inputs_hash_program.v',
                   'declaration',
                   'elements_inputs_hash_spec',
                   'Definition elements_inputs_hash_spec {alg : EFP.Algebra} : EFP.domain alg Ty.Unit '
                   'Word256 :=\n'
                   '  let term := EFP.CanonicalStructures.toAssertion alg in\n'
                   '  let core := Alg.Assertion.toCore term in\n'
                   '  @AC.comp _ _ _ core\n'
                   '    (@AC.pair _ _ _ core\n'
                   '      (@AC.comp _ _ _ core\n'
                   '        (@AC.pair _ _ _ core (@sha256_ctx8_init_spec core)\n'
                   '          (@AC.pair _ _ _ core (@elements_input_outpoints_hash_spec alg)\n'
                   '            (@elements_prim_words_hash_spec 2 5 Elements.InputSequence alg)))\n'
                   '        (@ctx8_addn_spec 6 term))\n'
                   '      (@elements_input_annexes_hash_spec alg))\n'
                   '    (@AC.comp _ _ _ core (@ctx8_addn_spec 5 term) (@ctx8_finalize_spec term)).\n'],
                  ['Coq/C/jet_elements_inputs_hash_program.v',
                   'statement',
                   'elements_inputs_hash_spec_parametric',
                   'Lemma elements_inputs_hash_spec_parametric : EFP.Parametric '
                   '(@elements_inputs_hash_spec).\n'],
                  ['Coq/C/jet_elements_inputs_hash_program.v',
                   'declaration',
                   'elements_inputs_hash_of',
                   'Definition elements_inputs_hash_of (e : Elements.env) : hash256 :=\n'
                   '  sha256_bytes_of\n'
                   '    (vector_values (Word 3) 6\n'
                   '       (from_hash256 (elements_input_outpoints_hash_of e),\n'
                   '        from_hash256 (elements_words_hash_of 2 5 (elements_input_sequences_words e))) '
                   '++\n'
                   '     vector_values (Word 3) 5 (from_hash256 (elements_input_annexes_hash_of e))).\n'],
                  ['Coq/C/jet_elements_inputs_hash_program.v',
                   'statement',
                   'elements_inputs_hash_spec_sem',
                   'Theorem elements_inputs_hash_spec_sem e :\n'
                   '  @elements_inputs_hash_spec elements_hash_alg tt e = Some (from_hash256 '
                   '(elements_inputs_hash_of e)).\n'],
                  ['Coq/C/jet_elements_inputs_hash_program.v',
                   'statement',
                   'elements_inputs_hash_program_local_spec',
                   'Theorem elements_inputs_hash_program_local_spec :\n'
                   '  application_jet_local_spec_sep f_simplicity_inputs_hash elements_ge Elements.env '
                   'Ty.Unit Word256\n'
                   '    (hash_getter_rep elements_inputs_hash_of 0 440 760)\n'
                   '    (fun a e => @elements_inputs_hash_spec elements_hash_alg a e).\n']],
 'blocks': [['Haskell/Simplicity/Elements/Programs/SigHash.hs',
             '  , inputsHash = (ctx8Init',
             '  , inputHash = (primitive',
             ' &&& (inputOutpointsHash &&& inputSequencesHash) >>> ctx8Addn vector64)\n'
             '             &&& inputAnnexesHash >>> ctx8Addn vector32 >>> ctx8Finalize\n\n']]}
