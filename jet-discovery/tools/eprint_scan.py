#!/usr/bin/env python3
"""Fetch only eprint metadata, preserve every result page, log every hit.

Search results include titles/authors/abstract snippets, not PDF contents. This is
an explicitly automated first-pass triage, not a full-text literature review.
"""
import argparse, csv, hashlib, html, json, re, time, urllib.parse, subprocess
from pathlib import Path

QUERIES = ['bitcoin', 'covenant', 'Schnorr', 'adaptor', 'threshold', '"hash-based"',
           '"post-quantum signatures"', 'BitVM', '"payment channels"', 'ecash',
           '"proof of reserves"', '"proofs of reserves"', '"blind Schnorr"', '"timed signatures"']
BASE = 'https://eprint.iacr.org'
ROOT = Path(__file__).resolve().parents[1]
VENDOR = ROOT / 'vendor-specs/eprint'
REPORTS = ROOT / 'reports/data'


def clean(s):
    return ' '.join(html.unescape(re.sub('<[^>]+>', ' ', s)).split())


def records(s):
    blocks = re.split(r'<a[^>]*class="paperlink"[^>]*>', s)[1:]
    out = []
    for block in blocks:
        paper_id = clean(block.split('</a>', 1)[0])
        title = re.search(r'<strong>(.*?)</strong>', block, re.S)
        abstract = re.search(r'<p[^>]*search-abstract[^>]*>(.*?)</p>', block, re.S)
        authors = re.search(r'<span class="fst-italic">(.*?)</span>', block, re.S)
        updated = re.search(r'Last updated: ([0-9-]+)', block)
        category = re.search(r'<small class="badge category[^>]*>(.*?)</small>', block, re.S)
        if re.fullmatch(r'20\d\d/\d+', paper_id) and title:
            out.append(dict(id=paper_id, title=clean(title[1]), abstract=clean(abstract[1]) if abstract else '',
                            authors=clean(authors[1]) if authors else '', updated=updated[1] if updated else '',
                            category=clean(category[1]) if category else ''))
    return out


def triage(r):
    t = (r['title'] + ' ' + r['abstract']).lower()
    title = r['title'].lower()
    # All rules are metadata-only. DEFER is a genuine verdict, not an exclusion.
    if any(x in title for x in ['bitvm', 'bitcoin script', 'pairing-based cryptography in bitcoin', 'pairing verification', 'garbl', 'groth16']):
        return 'CANDIDATE', 'Bridge/dispute verification: inspect SHA-256, bit commitments, BN254/pairing kernels; full protocol not implied implemented.'
    if any(x in title for x in ['blind schnorr', 'frost', 'timed signature', 'verifiable timed', 'sphincs', 'xmss', 'hash-based signature', 'winternitz', 'lamport']):
        return 'CANDIDATE', 'Concrete signature verifier or partial-share relation may run inside a UTXO authorization/dispute.'
    if any(x in title for x in ['covenant', 'adaptor', 'payment channel', 'proof of reserve', 'proofs of reserve', 'ecash']):
        return 'CANDIDATE', 'Possible Bitcoin application; map verification relation to UTXO authorization before implementation.'
    if any(x in title for x in ['selfish mining', 'consensus', 'proof-of-work', 'blockchain sharding', 'routing', 'transaction fee', 'mining pool', 'difficulty', 'ecd lp', 'quantum computer', 'side-channel']):
        return 'EXCLUDE', 'Metadata describes consensus/network/economic/attack analysis, not a new spending-condition verifier.'
    if 'schnorr' in t or 'threshold' in t:
        return 'DEFER', 'Final secp256k1 Schnorr signature already covered; inspect whether a distinct in-script accountability/partial-share relation is needed.'
    if any(x in t for x in ['signature', 'post-quantum', 'hash-based']):
        return 'DEFER', 'Potential non-native signature arithmetic; deployment path and complete verification spec require full-text review.'
    return 'DEFER', 'Metadata alone does not establish a Bitcoin spending-condition verifier; full-text review remains.'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--offline', action='store_true')
    ap.add_argument('--refresh', action='store_true')
    opts = ap.parse_args()
    VENDOR.mkdir(parents=True, exist_ok=True)
    manifest = []
    aggregate = {}
    for qi, query in enumerate(QUERIES):
        first_count = None
        offsets = [0]
        got = 0
        offset = 0
        while True:
            name = f'q{qi:02}-{offset:05}.html'
            target = VENDOR / name
            params = urllib.parse.urlencode(dict(q=query, submittedafter=2019, submittedbefore=2027, offset=offset))
            url = BASE + '/search?' + params
            if not opts.offline and (opts.refresh or not target.exists()):
                raw = subprocess.check_output(['curl', '--fail', '--location', '--silent', '--show-error', '--retry', '3', '--max-time', '60', url])
                target.write_bytes(raw)
                time.sleep(0.25)
            raw = target.read_bytes()
            s = raw.decode()
            count_match = re.search(r'(\d[\d,]*) results? sorted', s)
            if not count_match:
                raise RuntimeError(f'No result count in {name}; refusing silently incomplete scan')
            count = int(count_match[1].replace(',', ''))
            if first_count is None:
                first_count = count
            # eprint rounds the displayed total up to a page boundary until
            # the last page, where it reports the exact count.
            elif count > first_count or count < offset:
                raise RuntimeError(f'Inconsistent result count while paging {query}: {first_count} -> {count}')
            rows = records(s)
            got += len(rows)
            manifest.append(dict(query=query, offset=offset, results=count, url=url, file=name,
                                 sha256=hashlib.sha256(raw).hexdigest(), bytes=len(raw)))
            for r in rows:
                year = int(r['id'].split('/')[0])
                if not 2020 <= year <= 2026:
                    continue
                if r['id'] not in aggregate:
                    aggregate[r['id']] = dict(r, queries=[])
                aggregate[r['id']]['queries'].append(query)
            if offset + 100 >= count:
                if got != count:
                    raise RuntimeError(f'{query}: parsed {got} records vs advertised {count}')
                print(f'{query}: {count} records; {offset//100+1} pages', flush=True)
                break
            offset += 100
    (VENDOR / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    REPORTS.mkdir(parents=True, exist_ok=True)
    reviewed = json.loads((REPORTS / 'eprint-reviewed.json').read_text())
    with (REPORTS / 'eprint-scan.tsv').open('w') as out:
        fields = ['id', 'title', 'authors', 'updated', 'category', 'queries', 'verdict', 'reason', 'abstract', 'url', 'reviewed_verdict', 'programs', 'reviewed_reason']
        writer = csv.DictWriter(out, fields, delimiter='\t')
        writer.writeheader()
        for pid in sorted(aggregate, key=lambda p: tuple(map(int, p.split('/'))), reverse=True):
            r = aggregate[pid]
            verdict, reason = triage(r)
            writer.writerow(dict(r, queries='; '.join(r['queries']), verdict=verdict, reason=reason, url=BASE+'/'+pid, **reviewed.get(pid, {})))
    summary = {}
    for r in aggregate.values():
        verdict, _ = triage(r)
        summary[verdict] = summary.get(verdict, 0) + 1
    print(json.dumps(dict(unique=len(aggregate), triage=summary, pages=len(manifest)), indent=2))


if __name__ == '__main__':
    main()
