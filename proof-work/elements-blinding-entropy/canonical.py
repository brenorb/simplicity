"""Literal one-word8 canonical adapter; do not alter a live kernel input tree."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('blinding_literal_base', HERE / 'verify.py')
base = importlib.util.module_from_spec(sp)
sp.loader.exec_module(base)
s, g = base.s, base.g
MODULE = 'BlindingCanonical.BlindingEntropy'


def identity(work, external):
    base.tree(work)
    r = json.loads((HERE / 'RUN.json').read_text())
    if (r['candidate'] != str(work) or r['main_inputs'] != s.input_map() or
        r['staged_patch_sha256'] != s.index_hash() or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work) or
        r['tools_sha256'] != {'verify.py': s.sha((HERE / 'verify.py').read_bytes())}):
        raise ValueError('base current-source compilation identity differs')
    for field, suffix in [('sources_sha256', '.v'), ('objects_sha256', '.vo')]:
        for name, digest in r[field].items():
            if s.sha((work / 'Coq/C' / (name + suffix)).read_bytes()) != digest:
                raise ValueError('base checked source/object changed')
    source = external / 'BlindingEntropy.v'
    if (external == work or external == s.REPO or s.REPO in external.parents or source.is_symlink() or
        source.read_bytes() != (HERE / 'canonical/BlindingEntropy.v.source').read_bytes() or
        {p.name for p in external.glob('*.v')} != {'BlindingEntropy.v'}):
        raise ValueError('distinct canonical source/archive inventory required')
    s.safe_source(source.read_text(), str(source))
    return r, source, ['-Q', str(external), 'BlindingCanonical']


def compile(work, external):
    if (HERE / 'CANONICAL-RUN.json').exists():
        raise ValueError('canonical compilation already recorded')
    r, source, extra = identity(work, external)
    before, index = s.input_map(), s.index_hash()
    commands = {'literal-fresh': s.run(work,
        ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(source)], 'literal-fresh', 60)}
    results, definitions, deps = g.reports(work, [(MODULE, source)], 'literal', commands, extra)
    endpoint = MODULE + '.elements_issuance_blinding_entropy_hash_literal_local_spec'
    sem = MODULE + '.literal_issuance_blinding_entropy_hash_spec_sem'
    expected = {name: set() for name in results}
    expected.update({sem: {'FunctionalExtensionality.functional_extensionality_dep'}, endpoint: s.SIX})
    if (len(results), len(definitions)) != (6, 2) or deps != expected:
        raise ValueError('canonical complete statement/dependency inventory differs')
    identity(work, external)
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('canonical compilation changed current inputs/index')
    result = dict(candidate=str(work), external=str(external), module=MODULE,
        base_compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()),
        source_sha256=s.sha(source.read_bytes()), object_sha256=s.sha(source.with_suffix('.vo').read_bytes()),
        source_input_sha256=r['candidate_input_sha256'], staged_patch_sha256=index,
        tools_sha256={'canonical.py': s.sha(Path(__file__).read_bytes())},
        commands=commands, results=results, definitions=definitions, endpoint=endpoint,
        dependencies={name: sorted(ds) for name, ds in deps.items()},
        literal_one_word8=True, caller_cached_hashes_established=False,
        recursive_kernel_check=False, normal_registration=False, coverage_added=0, full_acceptance=False)
    s.changed({HERE / 'CANONICAL-RUN.json': json.dumps(result, indent=2) + '\n',
        **{HERE / (stem + '.log'): (work / (stem + '.log')).read_text() for stem in commands}})
    print('Literal one-word8 full C endpoint compiled and completely reported', flush=True)


def kernel(work, external):
    if (HERE / 'CANONICAL-KERNEL-RUN.json').exists():
        raise ValueError('canonical kernel already launched; inspect original process/terminal')
    r = json.loads((HERE / 'CANONICAL-RUN.json').read_text())
    original, source, extra = identity(work, external)
    if (r['external'] != str(external) or r['source_sha256'] != s.sha(source.read_bytes()) or
        r['object_sha256'] != s.sha(source.with_suffix('.vo').read_bytes()) or
        r['base_compile_sha256'] != s.sha((HERE / 'RUN.json').read_bytes()) or
        r['tools_sha256'] != {'canonical.py': s.sha(Path(__file__).read_bytes())}):
        raise ValueError('canonical compilation identity changed')
    before, index = s.input_map(), s.index_hash()
    command = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o '
               + ' '.join(extra) + ' ' + MODULE]
    launch = dict(candidate=str(work), external=str(external), command=command,
        compile_sha256=s.sha((HERE / 'CANONICAL-RUN.json').read_bytes()), recursive_kernel_check=False)
    s.changed({HERE / 'CANONICAL-KERNEL-RUN.json': json.dumps(launch, indent=2) + '\n'})
    row = s.run(work, command, 'literal-kernel', 3600)
    s.kernel.kernel((work / 'literal-kernel.log').read_text(),
                    sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    identity(work, external)
    if (s.input_map() != before or s.index_hash() != index or
        r['source_sha256'] != s.sha(source.read_bytes()) or
        r['object_sha256'] != s.sha(source.with_suffix('.vo').read_bytes())):
        raise ValueError('canonical kernel changed source/object/current inputs/index')
    r.update(recursive_kernel_check=True, kernel=row,
        kernel_launch_sha256=s.sha((HERE / 'CANONICAL-KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CANONICAL-CHECKED.json': json.dumps(r, indent=2) + '\n',
               HERE / 'literal-kernel.log': (work / 'literal-kernel.log').read_text()})
    print('Canonical one-word8 original-C endpoint recursively kernel-checked', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 4 or sys.argv[1] not in ['compile', 'kernel']:
        raise ValueError('usage: canonical.py compile|kernel PRIVATE_TREE EXTERNAL_PROOF_DIRECTORY')
    globals()[sys.argv[1]](Path(sys.argv[2]).resolve(), Path(sys.argv[3]).resolve())
