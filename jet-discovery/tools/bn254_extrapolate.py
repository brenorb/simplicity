#!/usr/bin/env python3
"""Price the dense BN254 arithmetic scenario from recorded local measurements."""
import argparse
import csv
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'reports/data'
IDS = ('eprint-bn254-fp-multiply', 'eprint-bn254-fp2-multiply')
CANDIDATE = 'bn254_fp_multiply'
SOURCE = 'src/JetDiscovery/Corpus/BN254.hs'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_json(name):
    return json.loads((DATA / name).read_text())


def require(ok, reason):
    if not ok:
        raise SystemExit(reason)


def check_log(name):
    record = load_json(name + '.json')
    require(record['exit_status'] == 0 and
            sha(DATA / (name + '.txt')) == record['log_sha256'],
            'Missing or failed measurement log: ' + name)
    require(record['source_sha256'][SOURCE] == sha(ROOT / SOURCE),
            'BN254 expression changed; repeat the standalone measurements')
    return record


def input_costs(runner):
    raw = check_log('bn254-typed-kernel-costs')
    typed = dict(line.split('=', 1) for line in
                 (DATA / 'bn254-typed-kernel-costs.txt').read_text().splitlines()[:5])
    if runner is None:
        evidence = check_log('bn254-pre-final-complete-analysis')
        entries = load_json('bn254-pre-final-measurements.json')
        require([r['id'] for r in entries] == list(IDS), 'Incomplete BN254 measurement packet')
        expected = (7, 5)
        for r, count in zip(entries, expected):
            require(len(r['vectors']) == count and all(v['passed'] for v in r['vectors']),
                    'Failed BN254 vectors: ' + r['id'])
            require(sha(DATA / (r['id'] + '-pre-final.snapshot.txt')) == r['snapshot_sha256'],
                    'Stale BN254 snapshot: ' + r['id'])
        require(len({r['fingerprint'] for r in entries}) == 1, 'Mixed BN254 fingerprints')
        wrapped = [r['native_mwu'] for r in entries]
        overlay = [r['isolated_candidates'][CANDIDATE] for r in entries]
        fingerprint = entries[0]['fingerprint']
        scope = 'two complete single-entry measurements; pre-final, no corpus-wide claim'
        wrapped_provenance = evidence['log_sha256']
    else:
        fingerprint = subprocess.check_output([str(runner.resolve()), 'fingerprint'],
                                              cwd=ROOT, text=True).strip()
        saved = DATA / 'run-fingerprint.txt'
        require(saved.is_file() and fingerprint and saved.read_text().strip() == fingerprint,
                'STALE: use the same frozen executable as the successful full corpus run')
        with (DATA / 'corpus-results.tsv').open() as stream:
            result_rows = list(csv.DictReader(stream, delimiter='\t'))
        with (DATA / 'candidate-impact.tsv').open() as stream:
            impacts = list(csv.DictReader(stream, delimiter='\t'))
        wrapped, overlay = [], []
        for ident, count in zip(IDS, (7, 5)):
            rows = [r for r in result_rows if r['id'] == ident]
            matches = [r for r in impacts if r['program'] == ident and r['candidate'] == CANDIDATE]
            require(len(rows) == len(matches) == 1 and
                    int(rows[0]['vectors_ok']) == int(rows[0]['vectors_total']) == count,
                    'Missing complete BN254 result: ' + ident)
            wrapped.append(int(rows[0]['cost_mwu']))
            require(int(matches[0]['current_mwu']) == wrapped[-1], 'Inconsistent BN254 impact: ' + ident)
            overlay.append(dict(cost_mwu_estimate=int(matches[0]['isolated_mwu_estimate']),
                                occurrences=int(matches[0]['occurrences'])))
        scope = 'fresh complete corpus results for wrapped terms; standalone typed arrow units'
        wrapped_provenance = sha(DATA / 'corpus-results.tsv')

    fp = int(typed['fp_kernel_native_mwu'])
    fp2 = int(typed['fp2_kernel_native_mwu'])
    price = int(typed['fp_jet_price_mwu_estimate'])
    # Isolated match leaves the Fp wrapper unchanged. Cross-check the inferred
    # call overhead from the measured Fp and both actual isolated scenarios.
    require([r['occurrences'] for r in overlay] == [1, 3], 'Unexpected BN254 match counts')
    call = overlay[0]['cost_mwu_estimate'] - (wrapped[0] - fp)
    require(call == price + 100 and wrapped[1] - 3 * (fp - call) == overlay[1]['cost_mwu_estimate'],
            'BN254 scenario does not reconcile with typed arrow and 100 mWU overhead')
    return dict(scope=scope, wrapped_run_fingerprint=fingerprint,
                wrapped_evidence_sha256=wrapped_provenance,
                typed_log_sha256=raw['log_sha256'],
                fp_kernel_cmr=typed['fp_kernel_cmr'], fp2_kernel_cmr=typed['fp2_kernel_cmr'],
                fp_kernel_native_mwu=fp, fp2_kernel_native_mwu=fp2,
                fp_wrapped_native_mwu=wrapped[0], fp2_wrapped_native_mwu=wrapped[1],
                fp_wrapped_isolated_mwu_estimate=overlay[0]['cost_mwu_estimate'],
                fp2_wrapped_isolated_mwu_estimate=overlay[1]['cost_mwu_estimate'],
                fp_jet_benchmark_analogy_mwu_estimate=price,
                fp_jet_call_mwu_estimate=call)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--pre-final', action='store_true', help='use the preserved two-entry analysis')
    mode.add_argument('--runner', type=Path, help='same frozen path as the full corpus run')
    args = parser.parse_args()
    units = input_costs(args.runner)
    p = 21888242871839275222246405745257275088696311157297823662689037894645226208583
    r = 21888242871839275222246405745257275088548364400416034343698204186575808495617
    u = 4965661367192848881
    assert p == 36*u**4 + 36*u**3 + 24*u**2 + 6*u + 1
    assert r == 36*u**4 + 36*u**3 + 18*u**2 + 6*u + 1
    k = 6*u + 2
    exponent = (p**12 - 1) // r
    miller_squares = k.bit_length() - 1
    miller_lines = (k.bit_length() - 1) + (k.bit_count() - 1) + 2
    final_exp_ops = (exponent.bit_length() - 1) + (exponent.bit_count() - 1)
    fp12_ops = miller_squares + 3*miller_lines + final_exp_ops
    fp2_mults = fp12_ops * (36 + 5)
    base_mults = fp2_mults * 3
    result = dict(label='ESTIMATE: dense arithmetic component only; no measured Groth16 verifier',
                  input_measurements=units, pairs=3, k_bits=k.bit_length(), k_popcount=k.bit_count(),
                  miller_shared_squares=miller_squares, miller_lines_per_pair=miller_lines,
                  final_exponent_bits=exponent.bit_length(), final_exponent_popcount=exponent.bit_count(),
                  final_exponent_dense_ops=final_exp_ops, total_fp12_dense_ops=fp12_ops,
                  fp2_muls_per_fp12=41, fp_muls_per_fp2=3,
                  total_fp2_multiplications=fp2_mults, total_base_multiplications=base_mults,
                  scenarios_mwu_estimate={
                      'native_fp_multiplication_only': base_mults * units['fp_kernel_native_mwu'],
                      'native_fp2_including_internal_add_subtract': fp2_mults * units['fp2_kernel_native_mwu'],
                      'hypothetical_fp_jet_calls_only': base_mults * units['fp_jet_call_mwu_estimate'],
                  },
                  excluded=['line coefficient generation and G2 arithmetic',
                            'G1 public-input linear combination', 'all Fp12 coefficient additions',
                            'point validation and subgroup checks', 'encoding/transcript costs'],
                  optimizations_not_modeled=['sparse line multiplication', 'specialized squaring',
                                             'Frobenius final exponentiation',
                                             'fixed-key line precomputation',
                                             'residue-check pairing verification'])
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
