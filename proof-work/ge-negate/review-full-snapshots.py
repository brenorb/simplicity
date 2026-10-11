"""Read-only full normal-build snapshot reconciliation, not acceptance.

Inherited contracts are byte-compared. New records are compared with the
reviewed deep report; ellipsis matches are diagnostics only, not certificates
for omitted terms. Actual source/kernel checks remain independently required.
"""
import argparse
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


LEGACY_DUPLICATE_DEFINITIONS = {
    ('C.jet_increment_spec', 'full_increment_word_spec'),
    ('C.jet_spec', 'full_increment8_spec'),
}


def rows(path, allowed_duplicates=frozenset()):
    records = [tuple(line.split()) for line in path.read_text().splitlines()
               if line.strip() and not line.startswith('#')]
    counts = Counter(records)
    duplicates = {row for row, count in counts.items() if count > 1}
    if (any(len(row) != 2 for row in records) or duplicates != set(allowed_duplicates)
            or any(counts[row] != 2 for row in duplicates)):
        raise ValueError('malformed/duplicate inventory: ' + str(path))
    return records


def chunks(text, names, allowed_duplicates=frozenset(), inherited_print_context=False):
    pattern = (r'(?m)^(?:(?:Variant|Record|Inductive) )?'
               r'(@?(?:[A-Za-z_][\w\']*\.)*(?:' +
               '|'.join(map(re.escape, sorted(names, key=len, reverse=True))) +
               r'))(?=(?:[ \t]*[:=]|(?:[ \t]+\?[\w]+)*\n[ \t]+:))')
    matches = list(re.finditer(pattern, text))
    if not matches or matches[0].start() != 0:
        raise ValueError('unparsed snapshot prefix')
    result = [(match[1].lstrip('@').split('.')[-1],
               text[match.start():matches[i + 1].start() if i + 1 < len(matches) else len(text)])
              for i, match in enumerate(matches)]
    counts = Counter(n for n, _ in result)
    duplicates = {n for n, count in counts.items() if count > 1}
    if not inherited_print_context and (duplicates != set(allowed_duplicates)
            or any(counts[n] != 2 for n in duplicates)):
        raise ValueError('duplicate snapshot records: ' + str({n: counts[n]
                                                             for n in sorted(duplicates)}))
    return result


# Only explicitly reviewed printing-context qualifications are removed.
# Never remove arbitrary prefixes or rewrite propositions/specifications.
QUALIFICATIONS = {
    'jet_frame_inv', 'jet_frame_layout', 'jet_output_layout', 'jet_secp_fe_nv',
    'jet_secp_frame', 'jet_secp_linkage', 'jet_secp_local_regions',
    'jet_secp_normalize_local', 'jet_secp_public_body', 'jet_secp_public_copy',
    'jet_secp_write_fe_wide_exec', 'jet_secp_write_fe_wide_values',
    'jet_secp_write_fe_wrapper', 'jet_sx_eval', 'jet_sx_exec', 'jet_sx_expr',
    'jet_sx_mem', 'jet_sx_rep', 'jet_sx_state', 'jet_secp_point_write_run',
    'jet_encoding', 'jet_input_layout', 'jet_readBit_layout', 'jet_secp_b32_exec',
    'jet_secp_canonical_normalize', 'jet_secp_canonical_zero', 'jet_secp_fe_math',
    'jet_secp_field_zero', 'jet_secp_fns', 'jet_secp_gej_public_entry',
    'jet_secp_odd_body', 'jet_secp_read_fe_numeric', 'jet_secp_wrapper_run',
    'jet_secp_write_fe_numeric', 'jet_sx_pure', 'jet_sx_zrep', 'jet_sx_zval',
    'jet_secp_point_write_field', 'jet_secp_gej_negate_literal',
    'jet_secp_gej_negate_boundary', 'jet_secp_point_negate_exec',
    'jet_secp_point_weak_exec', 'jet_secp_point_weak_values',
    'jet_secp_gej_infinity_layout', 'jet_secp_point_read_run',
    'jet_secp_point_weak_owned', 'jet_secp_point_negate_owned',
    'jet_secp_point_write_general_preservation', 'jet_secp_read_gej_fields',
    'jet_secp_write_gej_negated_literal', 'jet_secp_point_three_reads',
    'jet_secp_field_negate_storage', 'jet_secp_field_negate_values',
    'jet_secp_negate_literal_contract', 'jet_secp_canonical_negate',
    'jet_toZ', 'jet_word_repr', 'jet_secp_gej_predicate_body',
    'jet_secp_gej_public_body',
    'jet_secp_point_read_values',
    'jet_secp_point_field_bridge',
}


def norm(text, qualifications):
    if qualifications:
        pattern = r'\b(?:C\.)?(' + '|'.join(map(re.escape, sorted(qualifications))) + r')\.([A-Za-z_][\w]*)'
        text = re.sub(pattern, r'\2', text)
    text = re.sub(r'\bjets\.f_writeBit\b', 'f_writeBit', text)
    # The standard driver explicitly imports Simplicity.BitMachine whereas
    # the preliminary affine driver leaves its Cell type qualified.
    text = re.sub(r'\b(?:Simplicity\.)?BitMachine\.Cell\b', 'Cell', text)
    text = re.sub(r'\b(?:Simplicity\.)?Translate\.encode\b', 'encode', text)
    return re.sub(r'\s+', '', text)


def assumptions(path):
    lines = [line for line in path.read_text().splitlines() if line.strip()]
    result = {}
    for line in lines:
        name, value = line.split(' : ', 1)
        if name in result:
            raise ValueError('duplicate assumption record: ' + name)
        result[name] = [] if value == 'closed' else value.split(', ')
    return result


def review(archive, work, contracts_only=False):
    assembly_spec = importlib.util.spec_from_file_location('assembly', archive / 'assemble-candidate.py')
    assembly = importlib.util.module_from_spec(assembly_spec)
    assembly_spec.loader.exec_module(assembly)
    guards = assembly.verify(archive)
    receipt = json.loads((archive / 'ASSEMBLY.json').read_text())
    base = Path(receipt['baseline']) / 'Coq/C'
    candidate = Path(receipt['candidate']) / 'Coq/C'
    old_results = rows(base / 'jet_public_theorems.txt')
    old_defs = rows(base / 'jet_contract_definitions.txt', LEGACY_DUPLICATE_DEFINITIONS)
    all_results = rows(candidate / 'jet_public_theorems.txt')
    all_defs = rows(candidate / 'jet_contract_definitions.txt', LEGACY_DUPLICATE_DEFINITIONS)
    added = rows(archive / 'public-results.txt.source')
    defs = rows(archive / 'contract-definitions.txt.source')
    if all_results != old_results + added or all_defs != old_defs + defs:
        raise ValueError('inventories are not exact append-only extensions')
    names = {n for _, n in added + defs}
    if len(names) != 146 or names & {n for _, n in old_results + old_defs}:
        raise ValueError('unexpected/conflicting added names')
    all_names = {n for _, n in all_results + all_defs}
    legacy_names = {name for _, name in LEGACY_DUPLICATE_DEFINITIONS}
    # Printed inherited definitions include internal fields/constants sharing
    # display names across modules. Preserve their ENTIRE byte sequence, not
    # a dictionary that would silently discard repeated displayed names.
    baseline_text = (base / 'jet_contracts.expected').read_text()
    actual = chunks((candidate / 'jet_contracts.expected').read_text(), all_names,
                    inherited_print_context=True)
    baseline_records = chunks(baseline_text, all_names - names, inherited_print_context=True)
    actual_counts = Counter(name for name, _ in actual)
    if (len(actual) != len(baseline_records) + len(names)
            or any(actual_counts[n] != 1 for n in names)):
        raise ValueError('missing/duplicate new full contract records')
    inherited = ''.join(text for name, text in actual if name not in names)
    if inherited != baseline_text:
        raise ValueError('inherited contracts are not byte-identical')
    preliminary = json.loads((archive / 'PRELIMINARY-REVIEW.json').read_text())
    deep_path = work / 'contracts-review.out'
    if sha(deep_path) != preliminary['output_hashes']['contracts-review.out']:
        raise ValueError('reviewed deep report hash changed')
    deep_text = deep_path.read_text()
    if '...' in deep_text:
        raise ValueError('deep report truncated')
    deep = dict(chunks(deep_text, names))
    if set(deep) != names:
        raise ValueError('missing/unknown deep records')
    qualifications = QUALIFICATIONS | {module.split('.')[-1] for module, _ in added + defs}
    diagnostics = []
    for name, text in actual:
        if name not in names:
            continue
        current, expected = norm(text, qualifications), norm(deep[name], qualifications)
        if current == expected:
            continue
        position = 0
        for i, fragment in enumerate(current.split('...')):
            offset = expected.find(fragment, position)
            if offset < 0 or (i == 0 and offset != 0):
                mismatch = next((j for j, (a, b) in enumerate(zip(current, expected)) if a != b),
                                min(len(current), len(expected)))
                raise ValueError('unexpected contract difference: ' + name + '\n' +
                                 current[max(0, mismatch - 70):mismatch + 240] + '\n' +
                                 expected[max(0, mismatch - 70):mismatch + 240])
            position = offset + len(fragment)
        if '...' not in current or position != len(expected):
            raise ValueError('non-ellipsis contract difference: ' + name)
        diagnostics.append(name)
    expected_diagnostics = {'eval_owned_read_fe', 'affine_weak_run', 'affine_weak_tree',
                            'affine_negate_run', 'affine_negate_tree', 'owned_read_run',
                            'owned_read_tree', 'owned_write_run', 'owned_write_tree'}
    if set(diagnostics) != expected_diagnostics:
        raise ValueError('unexpected ellipsis supplement inventory: ' + str(diagnostics))
    if contracts_only:
        return {'candidate': receipt['candidate'], 'guards': guards,
                'inherited_contracts_byte_identical': True,
                'new_contract_records_reviewed': len(names), 'added_results': len(added),
                'added_definitions': len(defs), 'deep_ellipsis_supplements': sorted(diagnostics),
                'inherited_duplicate_definition_rows_preserved': sorted(legacy_names),
                'contract_snapshot_sha256': sha(candidate / 'jet_contracts.expected'),
                'assumptions_review_pending': True, 'full_acceptance': False}
    old_axioms = assumptions(base / 'jet_assumptions.expected')
    new_axioms = assumptions(candidate / 'jet_assumptions.expected')
    if any(new_axioms.get(n) != v for n, v in old_axioms.items()):
        raise ValueError('inherited assumption set changed')
    expected_axioms = json.loads((archive / 'PUBLIC-ASSUMPTION-REVIEW.json').read_text())['assumptions']
    if {n: v for n, v in new_axioms.items() if n not in old_axioms} != expected_axioms:
        raise ValueError('new assumption sets do not match reviewed reports')
    return {'candidate': receipt['candidate'], 'guards': guards,
            'inherited_contracts_byte_identical': True,
            'inherited_assumptions_identical': len(old_axioms),
            'added_results': len(added), 'added_definitions': len(defs),
            'new_assumptions_match_preliminary': True,
            'new_contract_records_reviewed': len(names),
            'inherited_duplicate_definition_rows_preserved': sorted(legacy_names),
            'deep_ellipsis_supplements': sorted(diagnostics),
            'candidate_snapshots': {n: sha(candidate / n)
                                    for n in ['jet_contracts.expected', 'jet_assumptions.expected']},
            'full_acceptance': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--archive', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--work', type=Path, required=True)
    parser.add_argument('--contracts-only', action='store_true',
                        help='partial receipt only; never authorizes acceptance')
    args = parser.parse_args()
    print(json.dumps(review(args.archive, args.work, args.contracts_only), indent=2))
