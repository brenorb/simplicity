        # Full context/hash-program contracts; these mutations are never compiled.
        for module, suffix in [
            ('C.jet_elements_inputs_hash_program', 'inputs_hash'),
            ('C.jet_elements_issuance_proofs_hash_program', 'issuance_range_proofs_hash'),
        ]:
            file = project / (module.replace('.', '/') + '.v')
            text = file.read_text()
            theorem = 'elements_' + suffix + '_program_local_spec'
            start = text.index('Theorem ' + theorem + ' :')
            stop = text.index('Proof.', start)
            block = text[start:stop]
            for old, new in [
                ('application_jet_local_spec_sep', 'False -> application_jet_local_spec_sep'),
                ('f_simplicity_' + suffix, 'f_simplicity_wrong_jet'),
                ('elements_ge Elements.env', 'wrong_ge Elements.env'),
                ('Elements.env', 'wrong_environment'),
                ('Ty.Unit Word256', 'Word32 Word256'),
                ('hash_getter_rep', 'wrong_rep'),
                ('elements_hash_alg', 'wrong_alg'),
                ('a e).', 'a e) -> True.'),
            ]:
                assert old in block, (suffix, old)
                file.write_text(text[:start] + block.replace(old, new, 1) + text[stop:])
                rejects(coverage.inventory, 'not a direct canonical jet theorem')
            file.write_text(text)
        assert coverage.inventory() == rows
