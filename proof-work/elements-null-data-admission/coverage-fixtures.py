        # Explicit contextual family; do not accept a hidden precondition,
        # wrong spec/relation/width, or substitute the broader local API.
        module = 'C.jet_elements_null_data_literal'
        theorem = 'elements_output_null_datum_literal_bitmachine_spec'
        file = project / (module.replace('.', '/') + '.v')
        shutil.copy2(SOURCE / (module.replace('.', '/') + '.v'), file)
        text = file.read_text()
        if not any(r['function'] == 'simplicity_output_null_datum' and r['proof'] for r in coverage.inventory()):
            manifest.write_text(manifest.read_text() + 'simplicity_output_null_datum ' + module + ' ' + theorem + '\n')
        if [module, theorem] not in coverage.records(audited, 2):
            audited.write_text(audited.read_text() + module + ' ' + theorem + '\n')
        declaration = 'Theorem ' + theorem + ' :'
        for old, new in [
            ('f_simplicity_output_null_datum', 'f_simplicity_output_script_hash'),
            ('elements_ge Elements.env', 'ge0 Elements.env'),
            ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
            ('(Ty.Prod Word32 Word32)', '(Ty.Prod Word64 Word32)'),
            ('ResultTy', 'Word256'),
            ('elements_null_data_environment_rep', '(fun _ _ _ _ => True)'),
            ('elements_output_null_datum_literal_spec', '(fun _ _ => Some (inl tt))'),
            (declaration, declaration + ' False ->'),
            ('application_jet_bitmachine_spec', 'application_jet_local_spec_sep'),
            ('elements_output_null_datum_literal_spec.', 'elements_output_null_datum_literal_spec -> True.'),
        ]:
            start = text.index(declaration)
            stop = text.index('Proof.', start)
            tail = text[start:stop]
            if old not in tail:
                import re
                match = re.search(r'\s+'.join(map(re.escape, old.split())), tail)
                assert match, old
                old = match[0]
            file.write_text(text[:start] + tail.replace(old, new, 1) + text[stop:])
            rejects(coverage.inventory, 'not a direct canonical jet theorem')
        file.write_text(text)
        assert coverage.inventory()
