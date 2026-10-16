        # The initialized lambda theorem has an exact constant/function/term
        # boundary, not an arbitrary Ready alias or the unrestricted old API.
        module = 'C.jet_secp_scalar_lambda_local'
        theorem = 'scalar_lambda_initialized_local_spec'
        file = project / (module.replace('.', '/') + '.v')
        shutil.copy2(SOURCE / (module.replace('.', '/') + '.v'), file)
        text = file.read_text()
        if not any(r['function'] == 'simplicity_scalar_multiply_lambda' and r['proof'] for r in coverage.inventory()):
            manifest.write_text(manifest.read_text() + 'simplicity_scalar_multiply_lambda ' + module + ' ' + theorem + '\n')
        if [module, theorem] not in coverage.records(audited, 2):
            audited.write_text(audited.read_text() + module + ' ' + theorem + '\n')
        declaration = 'Theorem ' + theorem + ' :'
        for old, new in [
            ('secp_jet_initialized_local_spec scalar_lambda_initialized', 'secp_jet_initialized_local_spec True'),
            ('secp_jet_initialized_local_spec scalar_lambda_initialized', 'secp_jet_local_spec'),
            ('f_simplicity_scalar_multiply_lambda', 'f_simplicity_scalar_square'),
            ('(Word 8) (Word 8)', '(Word 9) (Word 8)'),
            ('(Word 8) (Word 8)', '(Word 8) (Word 9)'),
            ('@canonical_scalar_multiply_lambda', '@canonical_scalar_square'),
            ('Alg.CoreFunSem', 'wrong_algebra'),
            (declaration, declaration + ' False ->'),
            ('Alg.CoreFunSem).', 'Alg.CoreFunSem) -> True.'),
        ]:
            start = text.index(declaration)
            stop = text.index('Proof.', start)
            body = text[start:stop]
            assert old in body, old
            file.write_text(text[:start] + body.replace(old, new, 1) + text[stop:])
            rejects(coverage.inventory, 'not a direct canonical jet theorem')
        file.write_text(text)
        assert coverage.inventory()
