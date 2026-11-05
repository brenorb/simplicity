#!/usr/bin/env python3
"""Fetch public period-ranking evidence, or validate an existing local capture.

No credentials, downloaded code execution, or third-party packages are used.
Network captures go into a NEW directory; existing snapshots are never replaced.
"""
import argparse
import csv
import datetime as dt
import hashlib
import json
from pathlib import Path
import re
import urllib.error
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
REV = "7a4ac0103af807380441e258adca3d3f78300738"
BASE = "https://raw.githubusercontent.com/soltop-app/soltop-oss/" + REV + "/"
SOURCES = [
    ("top-programs.json", "https://api.soltop.sh/api/top-programs", "Soltop operator API, advertised rolling 24h; full fixed top-20 result", "No data redistribution license stated; public factual response retained as research evidence"),
    ("summary.json", "https://api.soltop.sh/api/summary", "Soltop network summary, separate rolling 24h request", "No data redistribution license stated"),
    ("timeseries.json", "https://api.soltop.sh/api/timeseries", "Soltop network CU, 8-second buckets, advertised rolling 24h", "No data redistribution license stated"),
    ("openapi.yaml", "https://soltop.sh/docs/openapi.yaml", "Soltop official API schema v0.6.0", "Website documentation; no explicit license found"),
    ("api-docs.html", "https://soltop.sh/docs/index.html", "Soltop API authentication and anonymous limits", "Website documentation; no explicit license found"),
    ("homepage.html", "https://soltop.sh/", "Soltop operator identification and mainnet context", "Website content; no explicit license found"),
    ("source-README.md", BASE + "README.md", "Related open-source TUI documentation, not proof of deployed API implementation", "MIT; source-LICENSE"),
    ("source-parser.rs.txt", BASE + "src/rpc/parser.rs", "Related TUI parser, stored as non-executable data; deployed API equivalence unknown", "MIT; source-LICENSE"),
    ("source-LICENSE", BASE + "LICENSE", "Pinned related source license", "MIT"),
    ("etherscan-gastracker-response.html", "https://etherscan.io/gastracker?gasperiodsort=24", "Access attempt for Ethereum 24h gas ranking", "Access-failure body; no license grant inferred"),
    ("etherscan-topstat-response.html", "https://etherscan.io/topstat", "Alternate Ethereum explorer statistics access attempt", "Access-failure body; no license grant inferred"),
    ("solscan-fee-tracker-response.html", "https://solscan.io/analysis/fee-tracker", "Solana explorer 24h top-100 fee table with CU columns access attempt; HTTP success may contain only an empty static shell", "Website content; no license grant inferred"),
    ("solscan-dashboard-chunk.js.txt", "https://solscan.io/_next/static/chunks/6082-c836b7adc0413d42.js", "Inert frontend text identifies dashboard endpoint and chart selector", "No license stated; not imported or executed"),
    ("solscan-app-chunk.js.txt", "https://solscan.io/_next/static/chunks/pages/_app-94ab7b21f4be4167.js", "Inert frontend text identifies production api-v2.solscan.io/v2 base URL", "No license stated; not imported or executed"),
    ("solscan-top100-response.html", "https://api-v2.solscan.io/v2/analytics/fee_tracker/dashboard?chart_type=TOP_PROGRAMS_CONSUME_FEE_24H", "Actual Solscan dashboard data query access attempt; fee-ranked candidate set with CU columns, not necessarily global CU top-100", "Access-failure body; no license grant inferred"),
    ("mapping-jupiter-README.md", "https://raw.githubusercontent.com/jup-ag/instruction-parser/e6f77951377847c579112e6a16d8c17c5c092485/README.md", "Primary identification of Jupiter v6 program", "See mapping-jupiter-LICENSE; license must not be inferred if unavailable"),
    ("mapping-jupiter-LICENSE", "https://raw.githubusercontent.com/jup-ag/instruction-parser/e6f77951377847c579112e6a16d8c17c5c092485/LICENSE", "Primary Jupiter parser license evidence or access failure", "License evidence retained verbatim"),
    ("mapping-meteora-dlmm.md", "https://raw.githubusercontent.com/MeteoraAg/docs/edf57ecf775ffeb20aabbe80bfa1b1dd70be3493/developer-guides/dlmm/index.mdx", "Primary identification of DLMM program", "Documentation license not identified"),
    ("mapping-raydium-README.md", "https://raw.githubusercontent.com/raydium-io/raydium-library/72a22dcd6136fdd354c47d35aaa4b035652398c5/README.md", "Primary identification of Raydium CLMM program", "See mapping-raydium-LICENSE; license must not be inferred if unavailable"),
    ("mapping-raydium-LICENSE", "https://raw.githubusercontent.com/raydium-io/raydium-library/72a22dcd6136fdd354c47d35aaa4b035652398c5/LICENSE", "Primary Raydium library license evidence or access failure", "License evidence retained verbatim"),
]


def now():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def archive_body(status, body):
    """Do not publish request-origin IPs embedded in access-failure pages."""
    if status != 403:
        return body
    body = re.sub(rb"\b(?:[0-9]{1,3}\.){3}[0-9]{1,3}\b", b"[redacted-ipv4]", body)
    return re.sub(rb"\b(?:[0-9a-fA-F]{1,4}:){2,}[0-9a-fA-F:]+\b", b"[redacted-ipv6]", body)


def fetch(directory):
    directory.mkdir(parents=True, exist_ok=False)
    records = []
    for name, url, purpose, license_note in SOURCES:
        started = now()
        request = urllib.request.Request(url, headers={"User-Agent": "jet-discovery-public-ranking-research/1.0"})
        try:
            with urllib.request.urlopen(request, timeout=35) as response:
                body = response.read(5_000_001)
                status, headers, final_url = response.status, dict(response.headers), response.url
        except urllib.error.HTTPError as error:
            body = error.read(5_000_001)
            status, headers, final_url = error.code, dict(error.headers), error.url
        except (urllib.error.URLError, TimeoutError) as error:
            records.append(dict(file=None, source_url=url, purpose=purpose, retrieved_start_utc=started,
                                retrieved_end_utc=now(), error=str(error), license=license_note))
            continue
        if len(body) > 5_000_000:
            raise RuntimeError("Oversized response: " + url)
        response_bytes, response_hash = len(body), hashlib.sha256(body).hexdigest()
        body = archive_body(status, body)
        (directory / name).write_bytes(body)
        records.append(dict(file=name, source_url=url, final_url=final_url, purpose=purpose,
                            retrieved_start_utc=started, retrieved_end_utc=now(), http_status=status,
                            response_headers=headers, bytes=len(body), sha256=hashlib.sha256(body).hexdigest(),
                            http_response_bytes=response_bytes, http_response_sha256=response_hash,
                            sanitization="403 response IP literals redacted" if status == 403 else None,
                            source_revision=url.split("/")[5] if url.startswith("https://raw.githubusercontent.com/") else None,
                            license=license_note))
    manifest = dict(captured_utc=now(), chain="Solana mainnet-beta", ranking_provider="Soltop",
                    ranking_period="operator-advertised rolling last 24 hours; no explicit rank-window boundaries in response",
                    related_source_revision=REV, records=records)
    (directory / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    validate(directory, write_table=True)


def validate(directory, write_table=False):
    manifest = json.loads((directory / "manifest.json").read_text())
    for record in manifest["records"]:
        if record.get("file"):
            body = (directory / record["file"]).read_bytes()
            assert len(body) == record["bytes"], record["file"]
            assert hashlib.sha256(body).hexdigest() == record["sha256"], record["file"]
    records = {r.get("file"): r for r in manifest["records"]}
    for filename in ("top-programs.json", "summary.json", "timeseries.json", "openapi.yaml"):
        assert records[filename]["http_status"] == 200, filename
    top = json.loads((directory / "top-programs.json").read_text())
    assert len(top) == 20, "Not the schema's full fixed top-20 list"
    assert len({r["program_id"] for r in top}) == 20, "Duplicate program IDs"
    alphabet = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
    previous = None
    for row in top:
        value = 0
        for c in row["program_id"]:
            value = value * 58 + alphabet.index(c)
        size = (value.bit_length() + 7) // 8 + len(row["program_id"]) - len(row["program_id"].lstrip("1"))
        assert size == 32, row["program_id"]
        cu, count = int(row["total_cu_consumed"]), int(row["transaction_count"])
        assert cu >= 0 and count > 0
        assert previous is None or previous >= cu, "Non-descending CU ordering"
        assert abs(cu / count - float(row["avg_cu_per_transaction"])) < 0.000001
        assert 0 <= float(row["success_rate"]) <= 100
        previous = cu
    series = json.loads((directory / "timeseries.json").read_text())
    times = [dt.datetime.fromisoformat(r["bucket_8s"]) for r in series]
    assert len(times) == len(set(times)), "Duplicate network time buckets"
    assert times == sorted(times, reverse=True), "Unexpected network bucket order"
    assert all((a - b).total_seconds() == 8 for a, b in zip(times, times[1:])), "Missing 8-second network buckets"
    assert (max(times) - min(times)).total_seconds() == 86400, "Unexpected advertised network period"
    derived = dict(top_rows=len(top), top20_cu_sum=sum(int(r["total_cu_consumed"]) for r in top),
                   network_bucket_rows=len(times), network_bucket_label_min=min(times).isoformat(),
                   network_bucket_label_max=max(times).isoformat(),
                   network_bucket_duration_seconds=(max(times) - min(times)).total_seconds(),
                   caveat="Network bucket labels do not establish the separate ranking query's exact bounds, timezone, coverage, or accounting method")
    if write_table:
        fields = ["rank", "program_id", "total_cu_consumed", "transaction_count", "avg_cu_per_transaction", "success_rate"]
        with (directory / "top20.tsv").open("w", newline="") as out:
            writer = csv.DictWriter(out, fields, delimiter="\t", lineterminator="\n")
            writer.writeheader()
            writer.writerows(dict(rank=rank, **row) for rank, row in enumerate(top, 1))
        (directory / "validation.json").write_text(json.dumps(derived, indent=2) + "\n")
    else:
        assert json.loads((directory / "validation.json").read_text()) == derived
        with (directory / "top20.tsv").open() as source:
            saved = list(csv.DictReader(source, delimiter="\t"))
        assert len(saved) == 20
        for rank, (row, saved_row) in enumerate(zip(top, saved), 1):
            assert saved_row == {"rank": str(rank), **{k: str(v) for k, v in row.items()}}
    triage_path = directory / "utxo-triage.tsv"
    if triage_path.exists():
        with triage_path.open() as source:
            triage = list(csv.DictReader(source, delimiter="\t"))
        assert len(triage) == 20, "Incomplete UTXO triage"
        for rank, (row, verdict) in enumerate(zip(top, triage), 1):
            assert verdict["rank"] == str(rank) and verdict["program_id"] == row["program_id"]
            assert verdict["label"] and verdict["utxo_verdict"], "Missing triage verdict"
    for name in ("top20.tsv", "utxo-triage.tsv"):
        path = directory / name
        if path.exists():
            assert b"\r" not in path.read_bytes(), "Derived TSV must use LF: " + name
    print(json.dumps(derived, indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--fetch", metavar="NEW_DIRECTORY", type=Path, help="Fetch public sources into a new directory")
    group.add_argument("--check", metavar="DIRECTORY", type=Path, help="Offline hash, schema, ordering, and full-table checks")
    args = parser.parse_args()
    if args.fetch:
        fetch(args.fetch)
    else:
        validate(args.check)


if __name__ == "__main__":
    main()
