def raw_bitcoin_hash_contracts():
    """The reviewed complete target statements, not a cache-only helper shape."""
    spec = spec_from_file_location('raw_bitcoin_coverage_model', COQ / 'bitcoin-raw-program-source/source-model.py')
    model = module_from_spec(spec)
    spec.loader.exec_module(model)
    result = {}
    for path, kind, theorem, text in model.MODEL['declarations']:
        if (path == 'Coq/C/jet_bitcoin_hash_raw_program.v' and kind == 'statement'
                and theorem.startswith('bitcoin_') and theorem.endswith('_raw_program_local_spec')):
            name = 'simplicity_' + theorem.removesuffix('_raw_program_local_spec')
            head = re.match(r'Theorem\s+' + re.escape(theorem) + r'\s*:', text)
            if not head or name in result:
                raise ValueError('ambiguous raw Bitcoin hash contract model')
            result[name] = re.sub(r'\s+', '', text[head.end():])
    if set(result) != RAW_BITCOIN_HASH_JETS:
        raise ValueError('incomplete raw Bitcoin hash contract model')
    return result
