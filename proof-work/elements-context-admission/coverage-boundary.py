def elements_context_contracts():
    """Complete reviewed C-to-program statements, not cache-only helpers."""
    result = {}
    for folder in ['elements-annexes-source', 'elements-tapleaf-source',
                   'elements-tapenv-source', 'elements-outpoints-source']:
        spec = spec_from_file_location('elements_context_' + folder.replace('-', '_'), COQ / folder / 'source-model.py')
        model = module_from_spec(spec)
        spec.loader.exec_module(model)
        for path, kind, theorem, text in model.MODEL['declarations']:
            if kind == 'statement' and theorem.startswith('elements_') and theorem.endswith('_program_local_spec'):
                name = 'simplicity_' + theorem.removeprefix('elements_').removesuffix('_program_local_spec')
                head = re.match(r'Theorem\s+' + re.escape(theorem) + r'\s*:', text)
                if not head or name in result:
                    raise ValueError('ambiguous Elements context contract model')
                result[name] = re.sub(r'\s+', '', text[head.end():])
    if set(result) != ELEMENTS_CONTEXT_JETS:
        raise ValueError('incomplete Elements context contract model')
    return result
