#!/usr/bin/env python3
"""Fetch the full eprint metadata page of every deferred scan record.

    python3 tools/eprint_abstracts.py            # fetch missing pages (resumable)
    python3 tools/eprint_abstracts.py --check    # verify bytes against the manifest only

The deferred records come from reports/data/eprint-scan.tsv (verdict DEFER).
Each page https://eprint.iacr.org/<year>/<n> is stored unmodified as
vendor-specs-followup/eprint/abstracts/<year>-<n>.html; its URL, retrieval time, byte
count and SHA-256 go to vendor-specs-followup/eprint/abstracts/manifest.json.  Pages are
data: no downloaded script is executed.  Requests are sequential and spaced.
"""
import argparse
import csv
import hashlib
import json
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCAN = ROOT / 'reports' / 'data' / 'eprint-scan.tsv'
OUT = ROOT / 'vendor-specs-followup' / 'eprint' / 'abstracts'
MANIFEST = OUT / 'manifest.json'


def deferred_ids():
    with SCAN.open(newline='') as f:
        return [r['id'] for r in csv.DictReader(f, delimiter='\t') if r['verdict'] == 'DEFER']


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check', action='store_true')
    ap.add_argument('--delay', type=float, default=3.0)
    args = ap.parse_args()
    ids = deferred_ids()
    OUT.mkdir(parents=True, exist_ok=True)
    manifest = json.loads(MANIFEST.read_text()) if MANIFEST.exists() else {}
    if args.check:
        bad = [i for i in ids if i not in manifest or
               hashlib.sha256((OUT / manifest[i]['file']).read_bytes()).hexdigest() != manifest[i]['sha256']]
        print(f'{len(ids)} deferred ids, {len(ids) - len(bad)} verified, {len(bad)} missing or changed')
        sys.exit(1 if bad else 0)
    for n, ident in enumerate(ids):
        if ident in manifest:
            continue
        url = 'https://eprint.iacr.org/' + ident
        name = ident.replace('/', '-') + '.html'
        raw = None
        for attempt in range(6):
            try:
                raw = subprocess.check_output(['curl', '--fail', '--location', '--silent', '--show-error',
                                               '--max-time', '60', url])
                break
            except subprocess.CalledProcessError:
                time.sleep(60 * (attempt + 1))   # the archive rate-limits bursts; back off
        if raw is None:
            print('giving up on', url, flush=True)
            continue
        (OUT / name).write_bytes(raw)
        manifest[ident] = dict(file=name, url=url, bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest(),
                               retrieved=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()))
        MANIFEST.write_text(json.dumps(manifest, indent=1, sort_keys=True) + '\n')
        if n % 50 == 0:
            print(f'{len(manifest)}/{len(ids)}', flush=True)
        time.sleep(args.delay)
    MANIFEST.write_text(json.dumps(manifest, indent=1, sort_keys=True) + '\n')
    print(f'done: {len(manifest)}/{len(ids)}')


if __name__ == '__main__':
    main()
