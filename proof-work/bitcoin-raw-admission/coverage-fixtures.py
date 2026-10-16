        # These getters must target the whole canonical raw-data programs,
        # not just return unconstrained cached hashes. Do not compile fixtures.
        module = 'C.jet_bitcoin_hash_raw_program'
        file = project / (module.replace('.', '/') + '.v')
        text = file.read_text()
        for suffix in [
            'output_values_hash', 'output_scripts_hash', 'input_values_hash',
            'input_scripts_hash', 'input_sequences_hash', 'input_script_sigs_hash',
            'tappath_hash', 'tapleaf_hash', 'outputs_hash', 'input_utxos_hash',
            'tap_env_hash', 'input_outpoints_hash', 'input_annexes_hash',
            'inputs_hash', 'tx_hash', 'sig_all_hash',
        ]:
            theorem = 'bitcoin_' + suffix + '_raw_program_local_spec'
            start = text.index('Theorem ' + theorem + ' :')
            stop = text.index('Proof.', start)
            block = text[start:stop]
            for old, new in [
                ('application_jet_local_spec_sep', 'False -> application_jet_local_spec_sep'),
                ('f_simplicity_bitcoin_' + suffix, 'f_simplicity_bitcoin_wrong_jet'),
                ('bitcoin_ge raw_bitcoin_environment', 'ge0 raw_bitcoin_environment'),
                ('raw_bitcoin_environment', 'ext_environment'),
                ('Ty.Unit Word256', 'Word32 Word256'),
                ('raw_env_rep', 'wrong_rep'),
                ('raw_fullalg', 'fullalg'),
                ('raw_fullalg', 'wrong_alg'),
                ('a environment).', 'a environment) -> True.'),
            ]:
                assert old in block, (suffix, old)
                file.write_text(text[:start] + block.replace(old, new, 1) + text[stop:])
                rejects(coverage.inventory, 'not a direct canonical jet theorem')
            file.write_text(text)
        assert coverage.inventory() == rows
