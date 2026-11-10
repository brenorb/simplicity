#!/usr/bin/env python3
"""Security level of the custom Fibonacci STARK under the ethSTARK v1.2 bounds.

    python3 tools/stark_security.py

Source: ethSTARK Documentation, Version 1.2 (July 2023),
vendor-specs-followup/stark/ethstark-documentation-v1.2.pdf:
  * Eq. (19), section 5.10.1: conjectured security, lambda >= min{zeta + R s, log2|K|} - 1;
  * Eq. (20), section 5.10.2: provable IOP knowledge soundness, built from
    Theorem 4 (Eq. 11) and the batched FRI bound of Theorem 3 (Eq. 10,
    [BCIKS20, Theorem 8.3]);
  * Corollary 3 and section 7.1.1: provable security of the non-interactive
    (random-oracle) STARK from round-by-round soundness: lambda bits when every
    round error is at most 2^-(lambda+1) and the hash digest kappa >= 2 lambda + 3.

Parameters are those of reports/FIBONACCI-STARK.md.  The custom protocol is not
ethSTARK itself (no zero knowledge, a four-quotient Fibonacci AIR, DEEP with
four out-of-domain answers), so these are the published bounds applied to its
parameters, not a protocol-specific proof.
"""
import json
from math import log2, sqrt

P = 2 ** 31 - 1
params = dict(
    field_K=P ** 4,           # QM31: challenges, OOD point and FRI folding
    n=2 ** 16,                # evaluation domain |D|
    rho=2 ** 10 / 2 ** 16,    # degree bound 1024 over 65,536 points
    s=48,                     # FRI QUERY invocations
    folds=[2] * 10,           # ten binary folds to a constant
    h=10,                     # trace domain |H0| = 2^h = 1,024
    d_max=1024,               # smallest power of two above the composed constraint degree (< 1024)
    zeta=0,                   # no grinding
    kappa=256,                # SHA-256 commitments and transcript
)


def bits(x):
    return -log2(x)


def regimes(p, m):
    q, n, rho, s, t = p['field_K'], p['n'], p['rho'], p['s'], p['folds']
    ell = m / rho
    a = p['d_max'] / 2 ** p['h']
    deep_1 = ell / q
    deep_2 = (p['d_max'] + 2 ** p['h'] + a) * ell ** 2 / (q - a * n + 2 ** p['h'])
    query = (sqrt(rho) * (1 + 1 / (2 * m))) ** s
    # IOP knowledge soundness, Eq. (20)
    commit_iop = (m + 0.5) ** 7 * n ** 2 / (2 * rho ** 1.5 * q)
    fold_iop = (2 * m + 1) * (n + 1) * sum(t) / (sqrt(rho) * q)
    iop = min(bits(deep_1 + deep_2 + commit_iop + fold_iop), p['zeta'] + bits(query)) - 1
    # Round-by-round (section 7.1.1): commit term with constant 3; the first fold
    # round carries t_0 times it plus its own folding term (later rounds are smaller).
    commit_rbr = (m + 0.5) ** 7 * n ** 2 / (3 * rho ** 1.5 * q)
    fold_rbr = t[0] * commit_rbr + (2 * m + 1) * (n + 1) * t[0] / (sqrt(rho) * q)
    worst = max(deep_1, deep_2, commit_rbr, fold_rbr, query * 2 ** -p['zeta'])
    rom = min(bits(worst) - 1, (p['kappa'] - 3) / 2)
    return dict(m=m, iop_bits=iop, rom_bits=rom,
                terms_log2=dict(deep_1=log2(deep_1), deep_2=log2(deep_2), commit_iop=log2(commit_iop),
                                fold_iop=log2(fold_iop), commit_rbr=log2(commit_rbr), fold_rbr=log2(fold_rbr),
                                query=log2(query)))


def main():
    p = params
    R = -log2(p['rho'])
    conjectured = min(p['zeta'] + R * p['s'], log2(p['field_K'])) - 1
    best = max((regimes(p, m) for m in range(3, 40)), key=lambda r: r['rom_bits'])
    best_iop = max((regimes(p, m) for m in range(3, 40)), key=lambda r: r['iop_bits'])
    # The query count at which the query term stops binding, and the field size the
    # commit-phase term would need for 100 provable bits at this domain.
    out = dict(
        parameters={k: (v if k != 'field_K' else f'(2^31-1)^4 = 2^{log2(v):.3f}') for k, v in p.items()},
        conjectured_bits_eq19=round(conjectured, 2),
        conjectured_query_bits=R * p['s'],
        provable_iop_bits_eq20=round(best_iop['iop_bits'], 2), provable_iop_m=best_iop['m'],
        provable_rom_bits_cor3=round(best['rom_bits'], 2), provable_rom_m=best['m'],
        terms_log2_at_best_m={k: round(v, 2) for k, v in best['terms_log2'].items()},
        field_log2_needed_for_100_provable_bits=round(
            log2((3 + 0.5) ** 7 * p['n'] ** 2 / (3 * p['rho'] ** 1.5)) + 101 + log2(p['folds'][0]), 1),
    )
    print(json.dumps(out, indent=1))


if __name__ == '__main__':
    main()
