#!/usr/bin/env python3
"""Turn bench/ timings of C candidate sketches into benchmark-calibrated prices.

    python3 tools/bench_prices.py reports/data/candidate-c-bench.tsv

Inputs (all committed): the bench output (aggregate 'panel'/'sketch' rows and
per-input 'input' rows), Haskell/Simplicity/Bitcoin/Benchmarks.hs
(rawBenchmark), and the frozen ranking inputs under reports/data/.

Calibration.  Local nanoseconds t and upstream rawBenchmark r are related by an
affine fit r = a + s*t over the panel of existing jets, minimising relative
error.  The intercept absorbs per-call overhead in the upstream harness that this
loop does not have.  Leave-one-out errors over the panel are reported as the
calibration uncertainty.  A second, 'analogue' price scales by the jet the
frozen ESTIMATE was built from: r_ref * t_candidate / t_ref.

A candidate is priced near its worst case: the 95th percentile of per-input
times over its accepting reference vectors (the maximum is also reported; it
is dominated by timer noise for constant-time sketches).  For the generic WOTS
chain the worst valid path is priced from a regression on compressions done.  Prices are WU = r * 100 / rawBenchmark("CheckSigVerify"), the
normalisation of Simplicity.Bitcoin.Benchmarks.cost.  They remain ESTIMATES: the
sketches are not consensus code and the machine differs from upstream's.

Outputs:
  reports/data/candidate-bench-prices.tsv
  reports/data/candidate-bench-calibration.tsv
  reports/data/candidate-ranking-bench.json   first-order re-scoring, see below
"""
import collections
import csv
import json
import re
import sys
from decimal import Decimal
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'reports' / 'data'
BENCHMARKS = ROOT.parent / 'Haskell' / 'Simplicity' / 'Bitcoin' / 'Benchmarks.hs'

# Jet the frozen ESTIMATE was scaled from, and its multiplier there.
ANALOGUE = {
    'koalabear_add': 'Add32', 'm31_mul': 'FullMultiply32', 'qm31_mul': 'FeMultiply',
    'bn254_fp_multiply': 'FeMultiply', 'p256_fe_multiply': 'FeMultiply', 'ed25519_fe_multiply': 'FeMultiply',
    'keccak_f1600': 'Sha256Block', 'blake2s_compress': 'Sha256Block', 'blake2b_compress': 'Sha256Block',
    'blake3_compress_cv': 'Sha256Block', 'ripemd160_compress': 'Sha256Block', 'sha512_compress': 'Sha256Block',
    'sha256_pair': 'Sha256Block', 'sha256_wots_chain_16': 'Sha256Block', 'sha256_wots_chain_16_fixed': 'Sha256Block',
    'pubkey_unpack_neg': 'FeNormalize', 'signature_unpack': 'FeNormalize',
    'multiply_128': 'Multiply64', 'multiply_256': 'Multiply64', 'div_mod_256': 'DivMod128_64', 'div_mod_512': 'DivMod128_64',
}


def raw_benchmarks():
    return {k: float(v) for k, v in re.findall(r'rawBenchmark "(\w+)" = ([0-9.e+-]+)', BENCHMARKS.read_text())}


def fit(points):
    """Weighted least squares for r = a + s t with weights 1/r^2."""
    sw = swt = swtt = swr = swtr = 0.0
    for t, r in points:
        w = 1 / (r * r)
        sw += w; swt += w * t; swtt += w * t * t; swr += w * r; swtr += w * t * r
    det = sw * swtt - swt * swt
    s = (sw * swtr - swt * swr) / det
    a = (swr - s * swt) / sw
    return a, s


def read_bench(path):
    agg, inputs = {}, collections.defaultdict(list)
    for line in Path(path).read_text().splitlines():
        f = line.split('\t')
        if f[0] in ('panel', 'sketch'):
            agg[(f[0], f[1])] = dict(in_bits=int(f[2]), out_bits=int(f[3]), inputs=int(f[4]),
                                     mean=float(f[5]), median=float(f[6]), max=float(f[7]))
        elif f[0] == 'input':
            inputs[f[1]].append((int(f[2]), float(f[3]), f[4]))
    return agg, inputs


def wots_profile(rows):
    """Split sha256_wots_chain_16 timings by compressions performed.

    Input cells: six buffer chunks (32,16,8,4,2,1 bytes, each a tag bit then
    data/padding), the 64-bit compression count, the 256-bit midstate, the
    4-bit start index and the 128-bit node.  A step hashes buffer || 4 || 16
    bytes and finalises: one compression when the buffer holds at most 35
    bytes, two otherwise.
    """
    pts = []
    for _, ns, hexin in rows:
        bits = bin(int(hexin, 16))[2:].zfill(len(hexin) * 4)
        pos, length = 0, 0
        for size in (32, 16, 8, 4, 2, 1):
            if bits[pos] == '1':
                length += size
            pos += 1 + 8 * size
        start = int(bits[830:834], 2)
        per_step = 1 if length <= 35 else 2
        pts.append(((15 - start) * per_step, ns, length, start))
    n = len(pts)
    mx = sum(p[0] for p in pts) / n
    my = sum(p[1] for p in pts) / n
    beta = sum((p[0] - mx) * (p[1] - my) for p in pts) / sum((p[0] - mx) ** 2 for p in pts)
    alpha = my - beta * mx
    worst = [p for p in pts if p[0] == 30]
    profile18 = [p for p in pts if p[2] == 18 and p[3] == 0]
    return dict(alpha=alpha, beta=beta, n=n,
                ns_15=alpha + 15 * beta, ns_30=alpha + 30 * beta,
                observed_30=max((p[1] for p in worst), default=None), observed_30_count=len(worst),
                observed_18=max((p[1] for p in profile18), default=None))


def linear(pts):
    n = len(pts)
    mx = sum(x for x, _ in pts) / n
    my = sum(y for _, y in pts) / n
    beta = sum((x - mx) * (y - my) for x, y in pts) / sum((x - mx) ** 2 for x, _ in pts)
    return my - beta * mx, beta


def fixed_chain_profile(rows):
    """sha256_wots_chain_16_fixed does one compression per step from start to 14;
    the start nibble follows the 256-bit state and the 18 prefix bytes."""
    pts = []
    for _, ns, hexin in rows:
        bits = bin(int(hexin, 16))[2:].zfill(len(hexin) * 4)
        pts.append((15 - int(bits[400:404], 2), ns))
    alpha, beta = linear(pts)
    return dict(alpha=alpha, beta=beta, n=len(pts), ns_15=alpha + 15 * beta)


def main():
    bench_path = Path(sys.argv[1] if len(sys.argv) > 1 else DATA / 'candidate-c-bench.tsv')
    raw = raw_benchmarks()
    to_mwu = 100 / raw['CheckSigVerify'] * 1000
    agg, inputs = read_bench(bench_path)
    panel = {name: v for (kind, name), v in agg.items() if kind == 'panel'}
    points = [(v['mean'], raw[name]) for name, v in panel.items()]
    a, s = fit(points)
    calib = []
    loo = []
    for name, v in panel.items():
        rest = [(p['mean'], raw[n]) for n, p in panel.items() if n != name]
        a1, s1 = fit(rest)
        pred = a1 + s1 * v['mean']
        err = (pred - raw[name]) / raw[name]
        loo.append(abs(err))
        calib.append(dict(jet=name, local_mean_ns=f"{v['mean']:.3f}", raw_benchmark=f"{raw[name]:.3f}",
                          fitted_raw=f"{a + s * v['mean']:.3f}", leave_one_out_error=f"{100 * err:+.1f}%"))
    loo.sort()
    loo_median, loo_max = loo[len(loo) // 2], loo[-1]

    frozen = {r['candidate']: r for r in csv.DictReader((DATA / 'candidate-prices.tsv').open(), delimiter='\t')}
    prices = {}
    for (kind, name), v in sorted(agg.items()):
        if kind != 'sketch':
            continue
        ref = ANALOGUE[name]
        t_ref = panel[ref]['mean']
        times = sorted(ns for _, ns, _ in inputs[name])
        p95 = times[min(len(times) - 1, int(0.95 * len(times)))]
        fit_mwu = (a + s * p95) * to_mwu
        analogue_mwu = raw[ref] * p95 / t_ref * to_mwu
        prices[name] = dict(candidate=name, frozen_estimate_mwu=frozen[name]['cost_mwu_estimate'],
                            bench_mwu=str(round(fit_mwu)), analogue_mwu=str(round(analogue_mwu)),
                            analogue_jet=ref, p95_ns=f"{p95:.3f}", worst_ns=f"{v['max']:.3f}",
                            median_ns=f"{v['median']:.3f}", vectors_timed=str(v['inputs']),
                            method='ESTIMATE (C benchmark): affine panel calibration of the 95th-percentile input time')
    notes = {}
    if 'sha256_wots_chain_16' in inputs:
        w = wots_profile(inputs['sha256_wots_chain_16'])
        notes['sha256_wots_chain_16'] = w
        p = prices['sha256_wots_chain_16']
        p['profile18_mwu'] = str(round((a + s * w['ns_15']) * to_mwu))
        p['bench_mwu'] = str(round((a + s * w['ns_30']) * to_mwu))
        p['method'] = ('ESTIMATE (C benchmark): worst valid context, 30 compressions (15 steps with a buffer of '
                       'at least 36 bytes); profile18_mwu prices the matched 18-byte buffer at 15 compressions')
    if 'sha256_wots_chain_16_fixed' in inputs:
        w = fixed_chain_profile(inputs['sha256_wots_chain_16_fixed'])
        notes['sha256_wots_chain_16_fixed'] = w
        p = prices['sha256_wots_chain_16_fixed']
        p['bench_mwu'] = str(round((a + s * w['ns_15']) * to_mwu))
        p['method'] = 'ESTIMATE (C benchmark): start = 0, 15 compressions, from a regression on steps performed'
    # ecrecover: replace the 2 x Sha256Block Keccak proxy with the measured Keccak price.
    if 'keccak_f1600' in prices:
        old = int(frozen['ecrecover']['cost_mwu_estimate'])
        sha = raw['Sha256Block'] * to_mwu
        new = round(old - 2 * sha + int(prices['keccak_f1600']['bench_mwu']))
        prices['ecrecover'] = dict(candidate='ecrecover', frozen_estimate_mwu=str(old), bench_mwu=str(new),
                                   analogue_mwu='', analogue_jet='', worst_ns='', median_ns='', vectors_timed='',
                                   method=('ESTIMATE: frozen sum of existing secp256k1 jet benchmarks, with the '
                                           'Keccak proxy (2 x Sha256Block) replaced by the keccak_f1600 C benchmark'))
    fields = ['candidate', 'frozen_estimate_mwu', 'bench_mwu', 'analogue_mwu', 'analogue_jet', 'profile18_mwu',
              'p95_ns', 'worst_ns', 'median_ns', 'vectors_timed', 'method']
    with (DATA / 'candidate-bench-prices.tsv').open('w', newline='') as out:
        wr = csv.DictWriter(out, fields, delimiter='\t', lineterminator='\n', restval='')
        wr.writeheader()
        wr.writerows(prices.values())
    with (DATA / 'candidate-bench-calibration.tsv').open('w', newline='') as out:
        wr = csv.DictWriter(out, list(calib[0]), delimiter='\t', lineterminator='\n')
        wr.writeheader()
        wr.writerows(calib)
    new_prices = {n: int(p['bench_mwu']) for n, p in prices.items()}
    ranking = rescore(new_prices, frozen)
    fits = fit_changes(new_prices, frozen)
    summary = dict(bench=bench_path.name, intercept_raw=a, slope_raw_per_ns=s,
                   leave_one_out_median=loo_median, leave_one_out_max=loo_max,
                   panel=len(panel), wots=notes.get('sha256_wots_chain_16'), wots_fixed=notes.get('sha256_wots_chain_16_fixed'), fit_changes=fits, ranking=ranking)
    (DATA / 'candidate-ranking-bench.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({k: v for k, v in summary.items() if k not in ('ranking', 'fit_changes')}, indent=2))
    for f in fits:
        print('fit change:', f)
    for r in ranking:
        print(f"{r['rank']:>2} {r['family']:28s} score={float(r['score']):>14,.1f} frozen_rank={r['frozen_rank']}")


def fit_changes(new_prices, frozen):
    """Budget-applicable rows whose fixed-stack fit differs between the frozen
    ESTIMATE and the first-order benchmark repricing."""
    out = []
    for r in csv.DictReader((DATA / 'candidate-impact.tsv').open(), delimiter='\t'):
        name = r['candidate']
        if r['feasibility_applicable'] != 'true' or name not in new_prices or int(r['occurrences']) == 0:
            continue
        budget = int(r['effective_budget_wu']) * 1000
        old = int(r['isolated_mwu_estimate'])
        new = old + int(r['occurrences']) * (new_prices[name] - int(frozen[name]['cost_mwu_estimate']))
        if (old <= budget) != (new <= budget):
            out.append(dict(program=r['program'], candidate=name, budget_wu=budget / 1000,
                            frozen_isolated_wu=old / 1000, bench_isolated_wu=new / 1000,
                            bench_fits=new <= budget))
    return out


def context(classification):
    if classification.get('execution_context') == 'client_mode':
        return 'client'
    return {'full_spend_condition': 'native_full_spend', 'full_bounded_verifier': 'native_full_verifier',
            'protocol_component': 'protocol_component', 'arithmetic_or_hash_kernel': 'kernel'}[classification['kind']]


def rescore(new_prices, frozen):
    """First-order re-scoring with the frozen ranking policy.

    For each frozen isolated row, the repriced bound is
      isolated + occurrences * (new price - frozen price),
    where occurrences are the candidate's uses on the frozen worst path.  This
    holds exactly while that path stays the worst; if another path becomes worse
    the true bound is higher, so savings here are upper bounds when a price falls
    and exact-or-higher bounds otherwise.  Rows with zero occurrences keep their
    frozen saving.
    """
    classes = json.loads((DATA / 'corpus-classification.json').read_text())
    policy = json.loads((DATA / 'candidate-ranking-policy.json').read_text())
    frozen_rank = {r['family']: i + 1 for i, r in enumerate(json.loads((DATA / 'candidate-ranking.json').read_text()))}
    cands = policy['candidates']
    selected = collections.defaultdict(dict)
    for r in csv.DictReader((DATA / 'candidate-impact.tsv').open(), delimiter='\t'):
        name = r['candidate']
        delta = new_prices.get(name, int(frozen[name]['cost_mwu_estimate'])) - int(frozen[name]['cost_mwu_estimate'])
        saving = int(r['saving_mwu']) - int(r['occurrences']) * delta
        if saving <= 0:
            continue
        group = classes[r['program']]['count_group']
        family = cands[name]['family']
        old = selected[family].get(group)
        if old is None or saving > old[0]:
            selected[family][group] = (saving, context(classes[r['program']]))
    out = []
    for family in sorted({c['family'] for c in cands.values()}):
        rule = next(c for c in cands.values() if c['family'] == family)
        weighted = sum(Decimal(sv) * Decimal(str(policy['context_weights'][ctx])) for sv, ctx in selected[family].values())
        out.append(dict(family=family, groups=len(selected[family]),
                        weighted_saving_wu=str(weighted / 1000),
                        score=str(weighted * rule['generality'] / rule['burden'] / 1000),
                        frozen_rank=frozen_rank.get(family)))
    out.sort(key=lambda r: Decimal(r['score']), reverse=True)
    for i, r in enumerate(out):
        r['rank'] = i + 1
    return out


if __name__ == '__main__':
    main()
