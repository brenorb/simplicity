        # Exact startup contracts, including the four conditional Bitcoin helpers.
        file = project / 'C/jet_sha_canonical_startup.v'
        text = file.read_text()
        for name in sorted(coverage.SHA_STARTUP_JETS):
            theorem = name.removeprefix('simplicity_') + '_canonical_startup_spec'
            start = text.index('Theorem ' + theorem + ' :')
            stop = text.index('Proof.', start)
            block = text[start:stop]
            shape = 'sha_startup_partial_spec' if 'sha_startup_partial_spec' in block else 'sha_startup_total_spec'
            ty = 'sha256_ctx8_type' if 'sha256_ctx8_type' in block else 'Word256' if 'Word256' in block else '(Word 8)'
            alg = 'optalg' if 'optalg' in block else 'Alg.CoreFunSem'
            for old, new in [
                (shape, 'False -> ' + shape),
                (shape, 'wrong_startup_spec'),
                ('f_' + name, 'f_simplicity_wrong_jet'),
                (ty, 'wrong_type'),
                (alg, 'wrong_alg'),
                (').', ') -> True.'),
            ]:
                assert old in block, (name, old)
                file.write_text(text[:start] + block.replace(old, new, 1) + text[stop:])
                rejects(coverage.inventory, 'not a direct canonical jet theorem')
            if 'memcpy_model ->' in block:
                file.write_text(text[:start] + block.replace('memcpy_model ->', '', 1) + text[stop:])
            else:
                file.write_text(text[:start] + block.replace(' :', ' : memcpy_model ->', 1) + text[stop:])
            rejects(coverage.inventory, 'not a direct canonical jet theorem')
        file.write_text(text)
        assert coverage.inventory() == rows
