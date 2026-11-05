#!/usr/bin/env python3
"""Explicit ESTIMATE arithmetic-component model; does not verify pairings.

Input costs must come from the checked-in runner TSV. No cost is invented when
that measurement has not been generated: exit with a descriptive error instead.
"""
import csv, json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
p=21888242871839275222246405745257275088696311157297823662689037894645226208583
r=21888242871839275222246405745257275088548364400416034343698204186575808495617
u=4965661367192848881
assert p==36*u**4+36*u**3+24*u**2+6*u+1
assert r==36*u**4+36*u**3+18*u**2+6*u+1
k=6*u+2
exponent=(p**12-1)//r
miller_squares=k.bit_length()-1
miller_lines_per_pair=(k.bit_length()-1)+(k.bit_count()-1)+2
final_exp_ops=(exponent.bit_length()-1)+(exponent.bit_count()-1)
fp12_ops=miller_squares+3*miller_lines_per_pair+final_exp_ops
# Fp12 as Fp2[v]/(v^6-(9+i)): 36 schoolbook coefficient products
# plus 5 products by the fixed extension nonresidue. No sparsity used.
fp2_per_fp12=36+5
fp_per_fp2=3
base_mults=fp12_ops*fp2_per_fp12*fp_per_fp2
rows={x['id']:x for x in csv.DictReader((ROOT/'reports/data/corpus-results.tsv').open(),delimiter='\t')}
key='eprint-bn254-fp-multiply'
if key not in rows:
    raise SystemExit('BN254 measurement unavailable: run jet-discovery run to regenerate reports/data/corpus-results.tsv first')
row=rows[key]
if row['vectors_ok']!=row['vectors_total']:
    raise SystemExit('BN254 measurement has failing vectors; refusing extrapolation')
unit_mwu=int(row['cost_mwu'])
# This unit includes the harness wrapper (witness/equality/canonical checks).
# It is a deliberately conservative unit conversion for this scenario only.
result=dict(label='ESTIMATE: dense arithmetic component only; not a measured Groth16 verifier',
            source_entry=key, unit_includes_wrapper=True,
            fp_unit_mwu=unit_mwu,
            k_bits=k.bit_length(),k_popcount=k.bit_count(),miller_shared_squares=miller_squares,
            miller_lines_per_pair=miller_lines_per_pair, pairs=3,
            final_exponent_bits=exponent.bit_length(),final_exponent_popcount=exponent.bit_count(),
            final_exponent_dense_ops=final_exp_ops,total_fp12_dense_ops=fp12_ops,
            fp2_muls_per_fp12=fp2_per_fp12,fp_muls_per_fp2=fp_per_fp2,
            total_base_multiplications=base_mults, arithmetic_component_estimate_mwu=base_mults*unit_mwu,
            excluded=['line coefficient generation and G2 arithmetic','G1 public-input linear combination',
                      'field additions/subtractions','point validation and subgroup checks','encoding/transcript costs'],
            optimizations_not_modeled=['sparse line multiplication','specialized squaring','Frobenius final exponentiation',
                                       'fixed-key line precomputation','residue-check pairing verification'])
print(json.dumps(result,indent=2))
