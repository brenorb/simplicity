#!/usr/bin/env python3
"""Normalise go-ethereum's EIP-196 precompile vectors for the follow-up BN254 programs.

    python3 tools/bn254_vectors.py > reports/data/followup-bn254-vectors.tsv

The precompile reads calldata as a fixed-width input: shorter input is padded
with zero bytes and longer input is truncated (128 bytes for ECADD, 96 for
ECMUL).  This script applies that EVM ABI step and emits one row per vector:
kind, name, the input words in hex, and the expected output words.
Source: vendor-specs-followup/bn254/ (MANIFEST.md).
"""
import json
from pathlib import Path

SRC = Path(__file__).resolve().parents[1] / 'vendor-specs-followup' / 'bn254'
print('kind\tname\tinput_words\texpected_words')
for kind, fname, width in (('add', 'bn256Add.json', 128), ('mul', 'bn256ScalarMul.json', 96)):
    for v in json.loads((SRC / fname).read_text()):
        raw = bytes.fromhex(v['Input'])[:width].ljust(width, b'\0')
        words = [raw[i:i + 32].hex() for i in range(0, width, 32)]
        out = bytes.fromhex(v['Expected'])
        print('\t'.join([kind, v['Name'], ','.join(words), ','.join([out[:32].hex(), out[32:].hex()])]))
