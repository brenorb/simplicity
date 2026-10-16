def sha_startup_contracts():
    """Only the eighteen exact reviewed whole-C statements count."""
    spec = spec_from_file_location('sha_startup_fixed_coverage', COQ / 'sha-canonical-startup-source/source-model.py')
    model = module_from_spec(spec)
    spec.loader.exec_module(model)
    result = {}
    for path, kind, theorem, text in model.MODEL['declarations']:
        if (path == 'Coq/C/jet_sha_canonical_startup.v' and kind == 'statement' and
            theorem.endswith('_canonical_startup_spec')):
            name = 'simplicity_' + theorem.removesuffix('_canonical_startup_spec')
            head = re.match(r'Theorem\s+' + re.escape(theorem) + r'\s*:', text)
            if not head or name in result:
                raise ValueError('ambiguous whole SHA contract model')
            result[name] = re.sub(r'\s+', '', text[head.end():])
    if set(result) != SHA_STARTUP_JETS or len(result) != 18:
        raise ValueError('incomplete whole SHA contract model')
    return result
