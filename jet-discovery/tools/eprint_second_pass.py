#!/usr/bin/env python3
"""Second-pass triage of the deferred eprint records on full metadata pages.

    python3 tools/eprint_second_pass.py

The frozen scan (reports/data/eprint-scan.tsv) triaged 1,814 hits on search
snippets and left 1,595 as DEFER.  This pass reads each deferred paper's full
abstract, keywords and category from vendor-specs-followup/eprint/abstracts/
and applies the deterministic rules below, in order.  The question is the one
the corpus asks: does the paper define something a Bitcoin output would have to
*verify in script*, and if so, which primitive would that verifier need?

  MAPPED   the on-chain object is a standard signature or proof whose verifier
           is already measured: a BIP340/ECDSA/EdDSA signature (threshold,
           multi-, adaptor-free), BLS/pairing, lattice or hash-based signatures,
           or a SNARK/STARK verifier.  The mapped family is recorded.
  EXCLUDE  no in-script verification relation: consensus/agreement/broadcast,
           MPC/FHE/PIR/ORAM, encryption/KEM/secret sharing without a signature
           or proof output, attacks, side channels, hardware, or theory.
  PQ-OTHER a post-quantum signature family the corpus has not measured
           (isogeny, multivariate, code-based, MPC-in-the-head).
  REVIEW   explicit on-chain/Bitcoin/adaptor/covenant/channel/bridge relevance
           with a verification relation not covered above; these are reviewed
           individually in reports/data/eprint-second-pass-reviewed.json.
  DEFER    still not settled by the full abstract.

Outputs reports/data/eprint-second-pass.tsv and prints the counts.  The
reviewed overrides are merged by id.
"""
import csv
import html
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCAN = ROOT / 'reports' / 'data' / 'eprint-scan.tsv'
PAGES = ROOT / 'vendor-specs-followup' / 'eprint' / 'abstracts'
OUT = ROOT / 'reports' / 'data' / 'eprint-second-pass.tsv'
REVIEWED = ROOT / 'reports' / 'data' / 'eprint-second-pass-reviewed.json'


def page_fields(text):
    abstract = re.search(r'<h5 class="mt-3">Abstract</h5>\s*<p[^>]*>(.*?)</p>', text, re.S)
    keywords = re.findall(r'class="me-2 badge bg-secondary keyword">([^<]*)</a>', text)
    category = re.search(r'<small class="badge category[^"]*">([^<]*)</small>', text)
    title = re.search(r'<h3 class="mb-3">(.*?)</h3>', text, re.S)
    clean = lambda s: html.unescape(re.sub(r'<[^>]+>', ' ', s)).strip() if s else ''
    return dict(abstract=clean(abstract.group(1) if abstract else ''),
                keywords='; '.join(html.unescape(k) for k in keywords),
                category=clean(category.group(1) if category else ''),
                title=clean(title.group(1) if title else ''))


def has(text, *words):
    return any(re.search(w, text) for w in words)


ONCHAIN = (r'\bbitcoin', r'\butxo', r'\bscript\b', r'covenant', r'taproot', r'lightning', r'payment channel',
           r'\bon-?chain', r'smart contract', r'\bethereum', r'\bbridge', r'rollup', r'\bblockchain',
           r'cryptocurrenc', r'\bledger')
SIG = (r'signature', r'\bsign(ing|er)s?\b')


def classify(t, tk):
    """t: lower-cased title + keywords + abstract; tk: title + keywords only.
    Implementation and cryptanalysis cues are read from tk, because abstracts
    routinely mention attacks and implementations in passing."""
    onchain = has(t, *ONCHAIN)
    sig = has(t, *SIG)
    if has(t, r'adaptor signature', r'\bcovenant', r'payment channel', r'atomic swap', r'\bbitvm',
           r'proofs? of reserves?', r'\bvault', r'timed signature', r'time-lock puzzle', r'timelock'):
        return 'REVIEW', '', 'Bitcoin-relevant construction named in the abstract; individual review.'
    if has(tk, r'side[- ]channel', r'fault (attack|injection)', r'power analysis', r'electromagnetic', r'cache[- ]timing',
           r'rowhammer', r'\bfpga', r'cortex-m', r'\bneon\b', r'\bavx', r'\bgpu', r'embedded', r'microcontroller',
           r'hardware (implementation|accelerat|design)'):
        return 'EXCLUDE', 'implementation', 'Implementation engineering or physical attack on an existing scheme; no new verification relation.'
    if has(tk, r'\battack', r'cryptanalysis', r'\bbreak(s|ing)?\b', r'key[- ]recovery', r'shortest vector', r'lattice reduction',
           r'\bsolving\b', r'forgery attack', r'distinguisher'):
        return 'EXCLUDE', 'cryptanalysis', 'Cryptanalysis; no new verification relation.'
    if has(t, r'byzantine', r'\bconsensus', r'\bagreement\b', r'reliable broadcast', r'state machine replication',
           r'\bbft\b', r'atomic broadcast', r'leader election', r'random beacon', r'\bmvba\b'):
        return 'EXCLUDE', 'consensus', 'Consensus/agreement/broadcast protocol; no in-script spending relation.'
    if has(t, r'\bsnarks?\b', r'\bstarks?\b', r'groth16', r'\bplonk', r'zero-knowledge proof', r'\bzk-?snark', r'succinct argument',
           r'\bfri\b', r'polynomial commitment', r'lookup argument', r'\bfolding scheme', r'proof system'):
        if onchain:
            return 'MAPPED', 'proof-verifier', 'On-chain proof verification: maps to the measured STARK and BN254/Groth16 kernels.'
        return 'EXCLUDE', 'proof-system', 'Proof-system construction with no on-chain verification use in the abstract.'
    if sig and has(t, r'isogen', r'sqisign', r'csidh', r'\bmayo\b', r'\buov\b', r'oil and vinegar', r'multivariate',
                   r'code-based', r'less signature', r'code equivalence', r'\bfaest', r'mqom', r'sdith', r'\bhawk\b', r'\bperk\b', r'\bryde\b',
                   r'mpc-in-the-head', r'vole-in-the-head', r'isogeny group action'):
        return 'PQ-OTHER', 'pq-other-signature', 'Post-quantum signature family (isogeny/multivariate/code/MPCitH) not measured in the corpus.'
    if has(t, r'\bbls\b', r'pairing', r'bilinear'):
        if sig or onchain:
            return 'MAPPED', 'pairing', 'Verification is a pairing equation: maps to the BN254/BLS12-381 pairing item.'
        return 'EXCLUDE', 'pairing-non-signature', 'Pairing-based construction without a signature or on-chain output.'
    if has(t, r'lattice', r'dilithium', r'ml-dsa', r'falcon', r'\blwe\b', r'\bsis\b', r'module-lwe', r'\bntru'):
        if sig:
            return 'MAPPED', 'lattice-signature', 'Lattice signature: maps to the measured ML-DSA NTT/SHAKE kernels.'
        return 'EXCLUDE', 'lattice-non-signature', 'Lattice encryption/primitive without a signature verified in script.'
    if sig and has(t, r'hash-based', r'sphincs', r'slh-dsa', r'\bxmss', r'\blms\b', r'winternitz', r'\bwots'):
        return 'MAPPED', 'hash-signature', 'Hash-based signature: maps to the measured WOTS/SLH-DSA/XMSS/LMS programs.'
    if has(t, r'threshold', r'multi-?signature', r'multi-?party signing', r'\bfrost\b', r'musig', r'distributed key generation',
           r'\bdkg\b'):
        if has(t, r'\becdsa'):
            return 'MAPPED', 'ecdsa', 'Produces a standard ECDSA signature: maps to the ranked secp256k1_ecdsa_verify candidate.'
        if has(t, r'eddsa', r'ed25519'):
            return 'MAPPED', 'eddsa', 'Produces a standard EdDSA signature: maps to the measured Ed25519 verifier.'
        if has(t, r'schnorr', r'\bfrost\b', r'musig', r'bip-?340'):
            return 'MAPPED', 'schnorr', 'Produces a standard Schnorr signature: BIP340 jets verify it; FROST share accountability is measured.'
        if sig:
            return 'MAPPED', 'generic-signature', 'Threshold/multi-party signing whose output is verified as an ordinary signature.'
        return 'EXCLUDE', 'threshold-non-signature', 'Threshold key management/decryption/randomness without a signature verified in script.'
    if has(t, r'\bmpc\b', r'secure (multi-?party )?computation', r'homomorphic', r'\bfhe\b', r'oblivious', r'\bpir\b',
           r'\boram\b', r'private set intersection', r'garbled'):
        return 'EXCLUDE', 'mpc-fhe', 'MPC/FHE/PIR/ORAM construction; no in-script verification relation.'
    if not sig and not onchain and has(t, r'encryption', r'\bkem\b', r'key exchange', r'key encapsulation', r'secret sharing'):
        return 'EXCLUDE', 'encryption', 'Encryption/key exchange/secret sharing without a signature or on-chain output.'
    if onchain:
        return 'REVIEW', '', 'Blockchain use stated with a relation not mapped above; individual review.'
    if sig and has(t, r'\becdsa'):
        return 'MAPPED', 'ecdsa', 'ECDSA verification: maps to the ranked secp256k1_ecdsa_verify candidate.'
    if sig and has(t, r'schnorr'):
        return 'MAPPED', 'schnorr', 'Schnorr verification: BIP340 jets already verify it.'
    if sig:
        return 'DEFER', '', 'Signature scheme without a stated Bitcoin verification path.'
    return 'EXCLUDE', 'no-relation', 'No signature, proof or on-chain verification relation in the full abstract.'


def main():
    manifest = json.loads((PAGES / 'manifest.json').read_text())
    reviewed = json.loads(REVIEWED.read_text()) if REVIEWED.exists() else {}
    rows = []
    with SCAN.open(newline='') as f:
        for r in csv.DictReader(f, delimiter='\t'):
            if r['verdict'] != 'DEFER':
                continue
            entry = manifest.get(r['id'])
            if entry is None:
                rows.append(dict(id=r['id'], title=r['title'], verdict='MISSING', family='', reason='page not fetched',
                                 keywords='', category='', abstract_chars='0', reviewed_verdict='', reviewed_reason=''))
                continue
            fields = page_fields((PAGES / entry['file']).read_text(errors='replace'))
            text = ' '.join([r['title'], fields['keywords'], fields['abstract']]).lower()
            verdict, family, reason = classify(text, ' '.join([r['title'], fields['keywords']]).lower())
            rev = reviewed.get(r['id'], {})
            rows.append(dict(id=r['id'], title=r['title'], verdict=verdict, family=family, reason=reason,
                             keywords=fields['keywords'], category=fields['category'],
                             abstract_chars=str(len(fields['abstract'])),
                             reviewed_verdict=rev.get('verdict', ''), reviewed_reason=rev.get('reason', '')))
    with OUT.open('w', newline='') as out:
        w = csv.DictWriter(out, list(rows[0]), delimiter='\t', lineterminator='\n')
        w.writeheader()
        w.writerows(rows)
    counts = {}
    for r in rows:
        key = r['verdict'] + (':' + r['family'] if r['family'] else '')
        counts[key] = counts.get(key, 0) + 1
    print(json.dumps(dict(sorted(counts.items())), indent=1))
    print('reviewed overrides:', sum(1 for r in rows if r['reviewed_verdict']))
    empty = [r['id'] for r in rows if r['verdict'] != 'MISSING' and r['abstract_chars'] == '0']
    if empty:
        print('pages without a parsed abstract:', empty[:10], file=sys.stderr)


if __name__ == '__main__':
    main()
