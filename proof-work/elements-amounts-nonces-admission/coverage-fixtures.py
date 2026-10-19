        # Full C-to-canonical-program contracts; mutations are never compiled.
        for module, suffix, offset in [
            ('C.jet_elements_nonces_hash_program', 'output_nonces_hash', 56),
            ('C.jet_elements_amounts_hash_program', 'output_amounts_hash', 24),
            ('C.jet_elements_amounts_hash_program', 'input_amounts_hash', 248),
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
                ('0 ' + str(offset) + ' 760', '0 88 760'),
                ('elements_' + suffix + '_spec', 'wrong_spec'),
                ('elements_hash_alg', 'wrong_alg'),
                ('a e).', 'a e) -> True.'),
            ]:
                assert old in block, (suffix, old)
                file.write_text(text[:start] + block.replace(old, new, 1) + text[stop:])
                rejects(coverage.inventory, 'not a direct canonical jet theorem')
            file.write_text(text)
        assert coverage.inventory() == rows
