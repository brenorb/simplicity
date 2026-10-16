def elements_stream_contracts():
    """Exact reviewed whole-C programs, not merely a cached-field helper."""
    spec = spec_from_file_location('elements_stream_coverage_model', COQ / 'elements-stream-source/source-model.py')
    model = module_from_spec(spec)
    spec.loader.exec_module(model)
    result = {}
    for path, kind, theorem, text in model.MODEL['declarations']:
        if (path == 'Coq/C/jet_elements_words_hash_program.v' and kind == 'statement'
                and theorem.startswith('elements_') and theorem.endswith('_program_local_spec')):
            name = 'simplicity_' + theorem.removeprefix('elements_').removesuffix('_program_local_spec')
            head = re.match(r'Theorem\s+' + re.escape(theorem) + r'\s*:', text)
            if not head or name in result:
                raise ValueError('ambiguous Elements stream contract model')
            result[name] = re.sub(r'\s+', '', text[head.end():])
    if set(result) != ELEMENTS_STREAM_JETS:
        raise ValueError('incomplete Elements stream contract model')
    return result
