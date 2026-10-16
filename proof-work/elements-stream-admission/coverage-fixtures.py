        # Exact seven hash-stream contracts, never compiled as fake proofs.
        module = 'C.jet_elements_words_hash_program'
        file = project / (module.replace('.', '/') + '.v')
        text = file.read_text()
        for suffix in [
            'output_scripts_hash', 'output_range_proofs_hash',
            'output_surjection_proofs_hash', 'input_scripts_hash',
            'input_sequences_hash', 'input_script_sigs_hash', 'tappath_hash',
        ]:
            theorem = 'elements_' + suffix + '_program_local_spec'
            start = text.index('Theorem ' + theorem + ' :')
            stop = text.index('Proof.', start)
            block = text[start:stop]
            for old, new in [
                ('application_jet_local_spec_sep', 'False -> application_jet_local_spec_sep'),
                ('f_simplicity_' + suffix, 'f_simplicity_wrong_jet'),
                ('elements_ge Elements.env', 'ge0 Elements.env'),
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
