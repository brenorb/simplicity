"""Canonical asset/amount serializers, primitive pairing, loops and C getters.

Source fidelity is distinct from kernel checking and caller-cache construction.
The FE interface is the existing packed-field projection, not arbitrary FE input.
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
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


previous = load('amounts_inherited_source', HERE.parent / 'elements-nonces-source/check-source.py')
compact, extract = previous.compact, previous.extract


def check(repo):
    repo = Path(repo)
    result = previous.check(repo)
    parser = load('amounts_source_parser', repo / 'Coq/check-secp-predicates-specification.py')
    model = load('amounts_fixed_model', HERE / 'source-model.py').MODEL
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
            raise ValueError('Elements amounts selected source differs: ' + label)

    def line(path, name, expected):
        found = re.findall(r'(?m)^\s*' + re.escape(name) + r'\s*=([^\n]*)$', read(path))
        if len(found) != 1:
            raise ValueError('missing/ambiguous Elements amounts clause: ' + name)
        equal(found[0], expected, path + ':' + name)

    for path, kind, name, expected in model['declarations']:
        equal(extract(read(path), kind, name), expected, path + ':' + name)
    for path, start, stop, expected in model['blocks']:
        code = read(path)
        if code.count(start) != 1 or code.count(stop) != 1:
            raise ValueError('missing/ambiguous Elements amounts block: ' + start)
        equal(code.split(start, 1)[1].split(stop, 1)[0], expected, path + ':' + start)
    for path, name, expected in model['lines']:
        line(path, name, expected)
    for path, fragment in model['fragments']:
        head = fragment.split(':', 1)[0].strip()
        found = re.findall(r'(?m)^\s*' + re.escape(head) + r'\s*:[^\n]*$', read(path))
        if len(found) != 1:
            raise ValueError('missing/ambiguous Elements amounts carrier: ' + head)
        equal(found[0], fragment, path + ':' + head)
    for direction in ['output', 'input']:
        found = re.findall(r'\bbool\s+simplicity_' + direction + r'_amounts_hash\s*'
            r'\(frameItem\* dst, frameItem src, const txEnv\* env\)\s*\{([^{}]*)\}',
            read('C/elements/elementsJets.c'), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous original C amounts getter: ' + direction)
        equal(found[0], '(void) src; writeHash(dst, &env->tx->' + direction +
              'AssetAmountsHash); return true;', 'C ' + direction + ' getter')
    result['source_sha256'].update({str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)})
    result.update(selected_jets=['Elements.OutputAmountsHash', 'Elements.InputAmountsHash'],
        selected_primitives=['Elements.OutputAmount', 'Elements.OutputAsset',
                             'Elements.InputAmount', 'Elements.InputAsset'],
        canonical_amounts_source_review_complete=True, whole_contracts_reviewed=True,
        original_c_getters=2, shared_tagged_absorber_reviewed=True,
        canonical_amount_pair_program_reused=True, literal_asset_amount_serializers_reviewed=True,
        explicit_amount_bytes=8, confidential_amount_bytes=32,
        confidential_payload_interface='existing packed-field projection',
        arbitrary_word256_is_valid_field_element=False, caller_cached_hashes_established=False,
        formal_host_library_equivalence=False, kernel_checked_by_this_tool=False,
        normal_registration=False, coverage_added=0)
    return result


if __name__ == '__main__':
    print(json.dumps(check(Path(sys.argv[1]).resolve()), indent=2))
