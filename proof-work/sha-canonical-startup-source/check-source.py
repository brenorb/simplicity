"""Selected SHA canonical programs, whole C contracts and named startup state.

This is source-fidelity evidence, not a Haskell host-library verification,
kernel check, assertion-enabled build proof or normal jet registration.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def load(name, path):
    sp = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(module)
    return module


def compact(text):
    parts = re.split(r'("(?:\\.|[^"\\])*")', text)
    return ''.join(p if p.startswith('"') else re.sub(r'\s+', '', p) for p in parts)


def extract(code, kind, name):
    if kind == 'declaration':
        pattern = r'\b(?:Definition|Fixpoint|Let|Record)\s+' + re.escape(name) + r"(?![\w']).*?\.\s*(?=\n|$)"
    elif kind == 'statement':
        pattern = r'\b(?:Lemma|Theorem)\s+' + re.escape(name) + r"(?![\w']).*?(?=\bProof\.)"
    else:
        raise ValueError('unknown SHA source declaration kind')
    found = re.findall(pattern, code, re.S)
    if len(found) != 1:
        raise ValueError('missing/ambiguous SHA declaration: ' + name)
    return found[0]


def c_function(code, name):
    found = list(re.finditer(r'\b(?:static\s+)?bool\s+' + re.escape(name) + r'\s*\([^;{}]*\)\s*\{', code))
    if len(found) != 1:
        raise ValueError('missing/ambiguous complete SHA C function: ' + name)
    match = found[0]
    # All selected string literals are tag names, without braces. Ignore
    # braces inside any future string literal as well, rather than relying on it.
    token = re.compile(r'"(?:\\.|[^"\\])*"|[{}]')
    depth = 1
    for t in token.finditer(code, match.end()):
        depth += 1 if t[0] == '{' else -1 if t[0] == '}' else 0
        if depth == 0:
            return code[match.start():t.end()]
    raise ValueError('unclosed selected SHA C function: ' + name)


def check(repo):
    repo = Path(repo)
    parser = load('sha_canonical_source_parser', repo / 'Coq/check-secp-predicates-specification.py')
    model = load('sha_canonical_fixed_model', HERE / 'source-model.py').MODEL
    paths, cache = set(), {}

    def read(name):
        path = repo / name
        paths.add(path)
        if path not in cache:
            cache[path] = (re.sub(r'/\*.*?\*/|//[^\n]*', ' ', path.read_text(), flags=re.S)
                           if path.suffix == '.c' else parser.read_code(path))
        return cache[path]

    def equal(actual, expected, label):
        if compact(actual) != compact(expected):
            raise ValueError('selected SHA canonical source differs: ' + label)

    for path, kind, name, expected in model['declarations']:
        equal(extract(read(path), kind, name), expected, path + ':' + name)
    for path, start, stop, expected in model['blocks']:
        code = read(path)
        if code.count(start) != 1 or code.count(stop) != 1:
            raise ValueError('missing/ambiguous SHA source boundary: ' + path + ':' + start)
        equal(code.split(start, 1)[1].split(stop, 1)[0], expected, path + ':' + start)
    for path, pattern, expected in model['lines']:
        found = re.findall(pattern, read(path), re.M)
        if len(found) != 1:
            raise ValueError('missing/ambiguous SHA routing/type/helper: ' + path + ':' + pattern)
        equal(found[0], expected, path + ':' + pattern)
    for path, expected in model['files']:
        equal(read(path), expected, path)
    for path, name, expected in model['c_functions']:
        equal(c_function(read(path), name), expected, path + ':' + name)

    # Independently compare the 64 decimal/hex constants, including the first
    # round, not just the surrounding fixed text. This is a transcription
    # check of the actual programs, not an axiom about SHA's mathematics.
    hs = read('Haskell/Core/Simplicity/Programs/Sha256.hs')
    coq = extract(read('Coq/Simplicity/SHA256.v'), 'declaration', 'hashBlock')
    hk = re.search(r'k0:ks\s*=\s*\[([^]]*)\]', hs)
    ck = re.search(r'let k0 := (\d+)%Z in\s*let ks :=\s*\[([^]]*)\]%Z in', coq)
    if hk is None or ck is None:
        raise ValueError('missing SHA constant arrays')
    hks = [int(x.strip(), 16) for x in hk[1].split(',')]
    cks = [int(ck[1])] + [int(x.strip()) for x in ck[2].split(';')]
    if len(hks) != 64 or hks != cks:
        raise ValueError('SHA compression decimal/hex round constants disagree')
    return dict(selected_endpoints=18, whole_contracts_reviewed=True,
        named_startup_state_reviewed=True, canonical_source_review_complete=True,
        compression_and_context_programs_reviewed=True, bitcoin_tagged_programs_reviewed=True,
        round_constants_compared=64, complete_c_functions=len(model['c_functions']),
        coq_records=len(model['declarations']), haskell_blocks=len(model['blocks']),
        source_sha256={str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)},
        explicit_memcpy_endpoints=17, public_endpoint_inherited_assumptions=8,
        arbitrary_ready_parameter=False, kernel_checked_by_this_tool=False,
        formal_host_library_equivalence=False, optimized_dispatch_support=False,
        assertion_enabled_build_proved=False, normal_registration=False, coverage_added=0)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise ValueError('usage: check-source.py SOURCE_ROOT')
    print(json.dumps(check(Path(sys.argv[1]).resolve()), indent=2))
