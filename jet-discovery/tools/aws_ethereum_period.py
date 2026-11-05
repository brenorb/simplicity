#!/usr/bin/env python3
"""Read only the flat, selected columns of AWS's Ethereum day partitions.

No service credentials, SQL account, third-party modules, or executable
downloads. Unknown codecs/encodings/layouts fail rather than drop rows.
"""

from argparse import ArgumentParser
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
from struct import iter_unpack, unpack_from
from urllib.request import Request, urlopen
from xml.etree import ElementTree
import json
import re
import csv
import gzip
import io
import subprocess


TX_COLUMNS = (
    "block_number", "block_hash", "transaction_index", "to_address", "receipt_gas_used",
    "receipt_cumulative_gas_used", "receipt_status", "receipt_contract_address",
)
BLOCK_COLUMNS = (
    "number", "timestamp", "gas_used", "transaction_count", "hash", "parent_hash",
)
AWS = "https://aws-public-blockchain.s3.amazonaws.com/"
RPC = "https://ethereum-rpc.publicnode.com"
ARCHIVES = (
    ("alchemy","https://eth-mainnet.g.alchemy.com/public"),
    ("blast","https://eth-mainnet.public.blastapi.io"),
)
DAY = "2026-11-04"
S3 = {"s": "http://s3.amazonaws.com/doc/2006-03-01/"}


def require(condition, explanation):
    if not condition:
        raise ValueError(explanation)


class Bytes:
    def __init__(self, data):
        self.data = data
        self.pos = 0

    def read(self, count):
        end = self.pos + count
        require(0 <= count and end <= len(self.data), "truncated byte field")
        result = self.data[self.pos:end]
        self.pos = end
        return result

    def byte(self):
        require(self.pos < len(self.data), "truncated byte")
        n = self.data[self.pos]
        self.pos += 1
        return n

    def uint(self):
        n = 0
        for shift in range(0, 70, 7):
            b = self.byte()
            n |= (b & 127) << shift
            if b < 128:
                return n
        raise ValueError("overlong varint")

    def int(self):
        n = self.uint()
        return (n >> 1) ^ -(n & 1)

    def le(self, n):
        return int.from_bytes(self.read(n), "little")

    def end(self):
        require(self.pos == len(self.data), "unexpected trailing bytes")


def thrift_struct(r):
    last = 0
    result = {}
    while t := r.byte():
        kind = t & 15
        d = t >> 4
        last = last + d if d else r.int()
        require(last not in result, "duplicate Thrift field")
        result[last] = thrift_value(r, kind, True)
    return result


def thrift_value(r, kind, inline_bool=False):
    if kind in (1, 2):
        value = kind if inline_bool else r.byte()
        require(value in (1, 2), "invalid compact boolean")
        return value == 1
    if kind == 3:
        return r.byte()
    if kind in (4, 5, 6):
        return r.int()
    if kind == 7:
        return r.read(8)
    if kind == 8:
        return r.read(r.uint())
    if kind in (9, 10):
        h = r.byte()
        count = h >> 4
        if count == 15:
            count = r.uint()
        return [thrift_value(r, h & 15) for _ in range(count)]
    if kind == 11:
        count = r.uint()
        if count:
            h = r.byte()
            return [(thrift_value(r, h >> 4), thrift_value(r, h & 15))
                    for _ in range(count)]
        return []
    if kind == 12:
        return thrift_struct(r)
    raise ValueError(f"unsupported compact protocol type {kind}")


def footer(data):
    require(data[-4:] == b"PAR1", "missing Parquet footer magic")
    n = int.from_bytes(data[-8:-4], "little")
    require(0 < n <= len(data) - 8, "incomplete Parquet metadata")
    raw = data[-8-n:-8]
    r = Bytes(raw)
    meta = thrift_struct(r)
    r.end()
    require(meta[1] in (1, 2), "unknown Parquet file version")
    require(sum(rg[3] for rg in meta[4]) == meta[3], "row group count mismatch")
    return raw, meta


def range_plan(meta, names):
    """Plan exactly one compressed chunk range per selected row-group column."""
    schema = {col[4].decode(): col for col in meta[2][1:]}
    result = []
    for index, rg in enumerate(meta[4]):
        columns = {}
        for col in rg[1]:
            require(1 not in col, "external Parquet column object")
            m = col[3]
            if len(m[3]) == 1:
                columns[m[3][0].decode()] = m
        for name in names:
            m, s = columns[name], schema[name]
            require(s[1] == m[1] and s[3] in (0, 1), "only flat required/optional columns")
            require(m[4] in (0, 1), "only uncompressed or Snappy")
            require(m[5] == rg[3], "column cardinality differs from row-group count")
            start = m.get(11, m[9])
            require(4 <= start <= m[9] and m[7] > 0, "invalid column range")
            result.append(dict(row_group=index, name=name, rows=rg[3],
                               start=start, length=m[7], codec=m[4],
                               physical=m[1], optional=s[3] == 1,
                               encodings=m[2]))
    return result


def inspect(packet):
    for kind, columns in (("blocks", BLOCK_COLUMNS), ("transactions", TX_COLUMNS)):
        raw, meta = footer((packet/f"{kind}-tail.bin").read_bytes())
        plan = range_plan(meta, columns)
        print(kind, "rows", meta[3], "groups", len(meta[4]),
              "range bytes", sum(x["length"] for x in plan),
              "writer", meta.get(6, b"").decode())
        for x in plan[:len(columns)]:
            print(x)
        (packet/f"{kind}-footer.bin").write_bytes(raw)
        (packet/f"{kind}-ranges.json").write_text(json.dumps(plan, indent=2)+"\n")


def list_object(packet, kind):
    root = ElementTree.fromstring((packet/f"{kind}-listing.xml").read_bytes())
    expected_prefix = f"v1.0/eth/{kind}/date={DAY}/"
    require(root.findtext("s:Name", namespaces=S3) == "aws-public-blockchain" and
            root.findtext("s:Prefix", namespaces=S3) == expected_prefix and
            root.findtext("s:IsTruncated", namespaces=S3) == "false",
            "unexpected or incomplete listing")
    entries = root.findall("s:Contents", S3)
    require(len(entries) == 1, "expected exactly one object for the complete partition")
    fields = {name: entries[0].findtext("s:"+name, namespaces=S3)
              for name in ("Key", "ETag", "Size", "LastModified")}
    require(re.fullmatch(re.escape(expected_prefix) +
                         r"part-[0-9a-z-]+\.snappy\.parquet", fields["Key"]),
            "unexpected object key")
    require(re.fullmatch(r'"[a-f0-9]{32}(?:-[0-9]+)?"', fields["ETag"]), "invalid ETag")
    fields["Size"] = int(fields["Size"])
    return fields


def fetch_ranges(packet):
    jobs = []
    out = packet/"chunks"
    out.mkdir(exist_ok=True)
    existing = packet/"chunk-requests.json"
    prior = {(r["table"], r["row_group"], r["name"]):r
             for r in json.loads(existing.read_text())} if existing.exists() else {}
    for kind, columns in (("blocks", BLOCK_COLUMNS), ("transactions", TX_COLUMNS)):
        _, meta = footer((packet/f"{kind}-tail.bin").read_bytes())
        obj = list_object(packet, kind)
        jobs.extend((kind, obj, r) for r in range_plan(meta, columns))

    def fetch(job):
        kind, obj, r = job
        a, n = r["start"], r["length"]
        b = a+n-1
        url = AWS+obj["Key"]
        require(4 <= a <= b < obj["Size"] and n <= 20_000_000, "range outside bound")
        headers = {"Range": f"bytes={a}-{b}", "If-Match": obj["ETag"]}
        name = f"{kind}-{r['row_group']}-{r['name']}.bin"
        old = prior.get((kind,r["row_group"],r["name"]))
        same_source = old and old["url"] == url and old["request_headers"] == headers
        if same_source and (out/name).exists():
            blob = (out/name).read_bytes()
            require(len(blob) == n and sha256(blob).hexdigest() == old["sha256"],
                    "previously fetched range changed")
            return old
        start = datetime.now(timezone.utc).isoformat()
        with urlopen(Request(url, headers=headers), timeout=30) as response:
            require(response.geturl() == url and response.status == 206 and
                    response.headers["ETag"] == obj["ETag"] and
                    response.headers["Content-Range"] == f"bytes {a}-{b}/{obj['Size']}",
                    "range response does not match listed object and exact bounds")
            blob = response.read(n+1)
            require(len(blob) == n, "range body length mismatch")
            if same_source:
                require(sha256(blob).hexdigest()==old["sha256"],"refetched range differs from capture")
            (out/name).write_bytes(blob)
            if same_source:
                return old
            return dict(r, table=kind, url=url, request_headers=headers,
                        response_headers=dict(response.headers), status=response.status,
                        started_utc=start, ended_utc=datetime.now(timezone.utc).isoformat(),
                        file="chunks/"+name, sha256=sha256(blob).hexdigest())

    with ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(fetch, jobs))
    (packet/"chunk-requests.json").write_text(json.dumps(results, indent=2)+"\n")
    print(len(results), "complete compressed column chunks;",
          sum(r["length"] for r in results), "bytes")


def snappy(blob, expected):
    r = Bytes(blob)
    require(r.uint() == expected and 0 <= expected <= 64_000_000,
            "Snappy size differs from Parquet page metadata")
    out = bytearray()
    while r.pos < len(blob):
        tag = r.byte()
        typ, high = tag & 3, tag >> 2
        if typ == 0:
            n = (high if high < 60 else r.le(high-59)) + 1
            require(len(out) + n <= expected, "Snappy literal exceeds output")
            out.extend(r.read(n))
        else:
            if typ == 1:
                n, offset = 4 + (high & 7), (high >> 3) * 256 + r.byte()
            else:
                n, offset = 1 + high, r.le(1 << (typ - 1))
            require(0 < offset <= len(out) and len(out) + n <= expected,
                    "Snappy copy exceeds bounds")
            p = len(out)-offset
            if n <= offset:
                out.extend(out[p:p+n])
            else:
                out.extend((out[p:] * ((n+offset-1)//offset))[:n])
    require(len(out) == expected, "short Snappy page")
    return out


def hybrid(blob, width, count):
    """Parquet's RLE/bit-packed hybrid, with last-group zero padding ignored."""
    r = Bytes(blob)
    out = []
    require(0 <= width <= 32, "unexpected RLE width")
    mask = (1 << width) - 1
    while len(out) < count:
        h = r.uint()
        n = h >> 1
        left = count-len(out)
        require(n > 0, "empty hybrid run")
        if h & 1:
            require(8*n <= left+7, "bit-packed run exceeds count plus padding")
            # The bit stream is little-endian and each 8-value group consumes
            # exactly 'width' bytes, even when the values are not byte-sized.
            for _ in range(n):
                word = r.le(width)
                out.extend((word >> (width*j)) & mask for j in range(8))
        else:
            require(n <= left, "RLE run exceeds requested count")
            x = r.le((width+7)//8)
            require(x <= mask, "RLE value exceeds declared width")
            out.extend([x]*n)
    r.end()
    return out[:count]


def plain(blob, typ, count):
    if typ == 2:
        require(len(blob) == 8*count, "INT64 byte count mismatch")
        return [v for v, in iter_unpack("<q", blob)]
    if typ == 3:
        require(len(blob) == 12*count, "INT96 byte count mismatch")
        vals = []
        for nanos, jd in iter_unpack("<QI", blob):
            require(nanos < 86_400_000_000_000 and nanos % 1_000_000_000 == 0,
                    "unexpected non-integral UTC block timestamp")
            vals.append((jd-2_440_588)*86_400 + nanos//1_000_000_000)
        return vals
    require(typ == 6, f"unhandled physical type {typ}")
    r = Bytes(blob)
    vals = [bytes(r.read(r.le(4))) for _ in range(count)]
    r.end()
    return vals


def decode_column(blob, spec):
    r = Bytes(blob)
    dictionary = None
    out = []
    while r.pos < len(blob):
        h = thrift_struct(r)
        typ, uncomp, comp = h[1], h[2], h[3]
        page = r.read(comp)
        if spec["codec"] == 1:
            page = snappy(page, uncomp)
        else:
            require(comp == uncomp, "uncompressed page size mismatch")
        if typ == 2:
            require(dictionary is None and not out and h[7][2] in (0, 2),
                    "unexpected dictionary page")
            dictionary = plain(page, spec["physical"], h[7][1])
            continue
        require(typ == 0 and h[5][3] == 3, "unsupported page or definition-level layout")
        count, encoding = h[5][1], h[5][2]
        require(0 < count <= spec["rows"] - len(out), "data page exceeds row group")
        if spec["optional"]:
            length = unpack_from("<I", page)[0]
            require(length <= len(page)-4, "definition levels exceed page")
            levels = hybrid(page[4:4+length], 1, count)
            present = sum(levels)
            data = page[4+length:]
        else:
            levels = None
            present = count
            data = page
        if encoding == 0:
            values = plain(data, spec["physical"], present)
        elif encoding in (2, 8):
            require(dictionary is not None and data, "missing data dictionary or width")
            values = [dictionary[i] for i in hybrid(data[1:], data[0], present)]
        else:
            raise ValueError(f"unsupported value encoding {encoding}")
        if levels is None or present == count:
            out.extend(values)
        else:
            it = iter(values)
            out.extend(next(it) if d else None for d in levels)
    require(len(out) == spec["rows"], "decoded column count differs from footer")
    return out


def verified_rows(packet, table, names):
    records = json.loads((packet/"chunk-requests.json").read_text())
    _, meta = footer((packet/f"{table}-tail.bin").read_bytes())
    obj = list_object(packet, table)
    plan = range_plan(meta, names)
    requests = [r for r in records if r["table"] == table]
    require(len(requests) == len(plan), "missing or duplicate column ranges")
    by_group = defaultdict(dict)
    for record, item in zip(requests, plan, strict=True):
        require(all(record[key] == val for key,val in item.items()), "column range plan mismatch")
        expected_file = f"chunks/{table}-{item['row_group']}-{item['name']}.bin"
        require(record["file"] == expected_file and record["url"] == AWS+obj["Key"],
                "recorded column did not come from listed object")
        blob = (packet/expected_file).read_bytes()
        require(len(blob) == item["length"] and sha256(blob).hexdigest() == record["sha256"],
                "saved range differs from receipt")
        by_group[item["row_group"]][item["name"]] = item, blob
    for group, group_fields in by_group.items():
        require(list(group_fields) == list(names), "column order mismatch")
        columns = [decode_column(blob, item) for item,blob in group_fields.values()]
        yield from zip(*columns, strict=True)
        print(table, "row group", group, "decoded", len(columns[0]), flush=True)


def csv_out(path, header, rows):
    with path.open("w", newline="") as f:
        writer = csv.writer(f, delimiter="\t", lineterminator="\n")
        writer.writerow(header)
        writer.writerows(rows)


def stamp(seconds):
    return datetime.fromtimestamp(seconds, timezone.utc).isoformat()


def rank_period(packet):
    addresses = re.compile(rb"0x[0-9a-f]{40}")
    hashes = re.compile(rb"0x[0-9a-f]{64}")
    day_start = int(datetime.fromisoformat(DAY+"T00:00:00+00:00").timestamp())
    day_end = day_start+86_400
    blocks = sorted(verified_rows(packet, "blocks", BLOCK_COLUMNS))
    require(blocks, "no block rows")
    previous = None
    block_map = {}
    for b, t, gas, n, h, parent in blocks:
        require(isinstance(b, int) and day_start <= t < day_end and 0 <= gas and 0 <= n <= 65535
                and hashes.fullmatch(h) and hashes.fullmatch(parent), "invalid block metadata")
        if previous:
            p, tp, _, _, hp, _ = previous
            require(b == p+1 and t > tp and parent == hp, "nonconsecutive block chain")
        previous = b, t, gas, n, h, parent
        block_map[b] = (h, [None]*n)
    total = reverted = creation = creation_gas = creation_reverted = 0
    creation_sentinels = Counter()
    recipient = defaultdict(lambda: [0,0,0])
    boundary = []
    for b,h,i,address,gas,cumulative,status,created in verified_rows(packet, "transactions", TX_COLUMNS):
        expected_h, indices = block_map[b]
        require(h == expected_h and 0 <= i < len(indices) and indices[i] is None
                and 0 < gas <= cumulative and status in (0,1), "bad block/receipt identity or counters")
        indices[i] = (gas,cumulative)
        total += 1
        reverted += status == 0
        if b in (blocks[0][0],blocks[-1][0]):
            boundary.append((b,i,None if address in (None,b"None") else address.decode(),
                             gas,cumulative,status))
        if address in (None,b"None"):
            require(created is not None and addresses.fullmatch(created),
                    "null-recipient row lacks creation-receipt evidence")
            creation_sentinels[str(address)] += 1
            creation += 1
            creation_gas += gas
            creation_reverted += status == 0
        else:
            require(addresses.fullmatch(address) and created in (None,b"None",b""),
                    "invalid or creation-inconsistent recipient")
            r = recipient[address]
            r[0] += gas
            r[1] += 1
            r[2] += status == 0
    for b, _, gas, n, h, _ in blocks:
        indices = block_map[b][1]
        c = 0
        for rec in indices:
            require(rec is not None, "missing transaction index")
            g, cum = rec
            c += g
            require(cum == c, "cumulative receipt gas mismatch")
        require(c == gas and n == len(indices), "receipt totals disagree with block")
    full_gas = sum(b[2] for b in blocks)
    require(total == sum(b[3] for b in blocks) == creation+sum(v[1] for v in recipient.values())
            and full_gas == creation_gas+sum(v[0] for v in recipient.values())
            and reverted == creation_reverted+sum(v[2] for v in recipient.values()),
            "day totals fail reconciliation")
    ranks = sorted(recipient.items(), key=lambda item: (-item[1][0],item[0]))
    header = ["rank","recipient","receipt_gas_used","transactions","reverted_transactions"]
    ranked = [(i,address.decode(),*vals) for i,(address,vals) in enumerate(ranks, 1)]
    with (packet/"all-recipients.tsv.gz").open("wb") as base:
        with gzip.GzipFile(filename="", mode="wb", fileobj=base, mtime=0) as raw:
            with io.TextIOWrapper(raw, encoding="ascii", newline="") as f:
                writer = csv.writer(f, delimiter="\t", lineterminator="\n")
                writer.writerow(header)
                writer.writerows(ranked)
    csv_out(packet/"top100-recipients.tsv", header, ranked[:100])
    csv_out(packet/"all-blocks.tsv",
            ["block_number","time_utc","header_gas_used","transactions","hash","parent_hash"],
            ((b,stamp(t),gas,n,h.decode(),parent.decode()) for b,t,gas,n,h,parent in blocks))
    csv_out(packet/"boundary-aws-transactions.tsv",
            ["block_number","transaction_index","to","gas_used","cumulative_gas_used","status"],
            sorted(boundary))
    result = dict(day_start_utc=stamp(day_start), day_end_utc_exclusive=stamp(day_end),
                  block_count=len(blocks), first_block=blocks[0][0], first_time=stamp(blocks[0][1]),
                  last_block=blocks[-1][0], last_time=stamp(blocks[-1][1]), transactions=total,
                  total_header_gas=full_gas, total_receipt_gas=full_gas,
                  reverted_transactions=reverted, distinct_nonnull_recipients=len(recipient),
                  contract_creation_transactions=creation, contract_creation_gas=creation_gas,
                  reverted_contract_creations=creation_reverted,
                  creation_to_sentinels=dict(creation_sentinels),
                  gas_reconciliation="all tx indices, block hashes, per-index cumulative gas, header gas and counts equal")
    (packet/"aggregation.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


def rpc_call(packet, tag, calls, endpoint=RPC):
    """Save an exact public read-only JSON-RPC batch and its bounded reply."""
    allowed = {"eth_chainId", "eth_getBlockByNumber", "eth_getBlockReceipts", "eth_getCode"}
    require(all(method in allowed for method, _ in calls), "not a read-only batch")
    request = [dict(jsonrpc="2.0", id=i, method=m, params=p)
               for i,(m,p) in enumerate(calls,1)]
    body = json.dumps(request, separators=(",",":")).encode()
    request_path = packet/f"rpc-{tag}-request.json"
    response_path = packet/f"rpc-{tag}-response.json"
    headers_path = packet/f"rpc-{tag}-headers.txt"
    request_path.write_bytes(body)
    start = datetime.now(timezone.utc).isoformat()
    cap = 12_000_000
    result = subprocess.run(["curl","-sS","--max-time","45","--max-filesize",str(cap),
                             "-D",str(headers_path),"-o",str(response_path),"-w","%{http_code}",
                             "-H","Content-Type: application/json","--data-binary","@"+str(request_path),endpoint],
                            capture_output=True,text=True)
    raw = response_path.read_bytes() if response_path.exists() else b""
    record = dict(url=endpoint, started_utc=start, ended_utc=datetime.now(timezone.utc).isoformat(),
                  http_status=result.stdout, curl_exit_status=result.returncode,
                  response_headers_file=headers_path.name, response_bytes=len(raw),
                  request_sha256=sha256(body).hexdigest(), response_sha256=sha256(raw).hexdigest())
    (packet/f"rpc-{tag}-provenance.json").write_text(json.dumps(record,indent=2)+"\n")
    require(result.returncode==0 and result.stdout=="200" and len(raw)<=cap,
            f"RPC batch {tag} failed: curl {result.returncode}, HTTP {result.stdout}")
    rows = json.loads(raw)
    require(isinstance(rows,list) and len(rows)==len(calls), "incomplete RPC batch")
    by_id = {r["id"]:r for r in rows}
    require(set(by_id)==set(range(1,len(calls)+1)), "duplicate or missing RPC identifiers")
    return [by_id[i] for i in range(1,len(calls)+1)]


def tab(path):
    with path.open(newline="") as f:
        return list(csv.DictReader(f,delimiter="\t"))


def verify_rpc(packet):
    a = json.loads((packet/"aggregation.json").read_text())
    first, last = a["first_block"],a["last_block"]
    in_scope = tab(packet/"all-blocks.tsv")
    chain = rpc_call(packet,"boundaries", [("eth_chainId",[])] +
                     [("eth_getBlockByNumber",[hex(b),False]) for b in (first-1,first,last,last+1)] +
                     [("eth_getBlockByNumber",["finalized",False])])
    chain_id, prev, start, end, after, finalized = (row["result"] for row in chain)
    require(chain_id == "0x1" and int(finalized["number"],16) >= last,
            "RPC is not Ethereum mainnet or day is not finalized")
    require([int(row["number"],16) for row in (prev,start,end,after)] == [first-1,first,last,last+1],
            "wrong RPC boundary heights")
    require(stamp(int(prev["timestamp"],16)) < a["day_start_utc"] <= stamp(int(start["timestamp"],16))
            and stamp(int(end["timestamp"],16)) < a["day_end_utc_exclusive"] <= stamp(int(after["timestamp"],16)),
            "RPC does not bracket the exact UTC period")
    require(start["parentHash"]==prev["hash"] and after["parentHash"]==end["hash"],
            "RPC adjacent boundary block chain mismatch")
    for row,aws in ((start,in_scope[0]),(end,in_scope[-1])):
        require(row["hash"]==aws["hash"] and row["parentHash"]==aws["parent_hash"]
                and stamp(int(row["timestamp"],16))==aws["time_utc"]
                and int(row["gasUsed"],16)==int(aws["header_gas_used"])
                and len(row["transactions"])==int(aws["transactions"]),
                "AWS boundary block disagrees with independent RPC")
    receipts = rpc_call(packet,"boundary-receipts",
                        [("eth_getBlockReceipts",[hex(b)]) for b in (first,last)])
    got = []
    for reply,block in zip(receipts,(start,end),strict=True):
        rows = reply["result"]
        require(len(rows)==len(block["transactions"]), "incomplete independent block receipts")
        for r in rows:
            i = int(r["transactionIndex"],16)
            require(r["blockHash"]==block["hash"] and r["transactionHash"]==block["transactions"][i],
                    "independent receipt position or hash disagrees")
            got.append((int(r["blockNumber"],16),i,r["to"] or "",int(r["gasUsed"],16),
                        int(r["cumulativeGasUsed"],16),int(r["status"],16)))
    expected = [(int(r["block_number"]),int(r["transaction_index"]),r["to"],int(r["gas_used"]),
                 int(r["cumulative_gas_used"]),int(r["status"]))
                for r in tab(packet/"boundary-aws-transactions.tsv")]
    require(sorted(got)==expected, "AWS boundary transaction columns disagree with independent RPC")
    (packet/"rpc-boundary-validation.json").write_text(json.dumps(
        dict(chain_id=chain_id, first_block=first, last_block=last, previous_time=stamp(int(prev["timestamp"],16)),
             next_time=stamp(int(after["timestamp"],16)), finalized_height=int(finalized["number"],16),
             independent_receipts_compared=len(got)),indent=2)+"\n")
    print("RPC Ethereum mainnet boundary confirmation;",len(got),"complete boundary receipts reconciled")


def rank_contracts(packet):
    a = json.loads((packet/"aggregation.json").read_text())
    last = a["last_block"]
    require((packet/"rpc-boundary-validation.json").exists(),"verify chain boundary before code lookup")
    block = tab(packet/"all-blocks.tsv")[-1]
    block_selector = {"blockHash":block["hash"],"requireCanonical":True}
    candidates = tab(packet/"top100-recipients.tsv")
    checked = []
    selected = []
    for offset in range(0,len(candidates),20):
        rows = candidates[offset:offset+20]
        calls = [("eth_chainId",[])] + [("eth_getCode",[r["recipient"],block_selector]) for r in rows]
        sources = [rpc_call(packet,f"archive-{name}-code-{offset+1:03}",calls,url)
                   for name,url in ARCHIVES]
        require(all(s[0].get("result")=="0x1" for s in sources),"archive is not Ethereum mainnet")
        for i,row in enumerate(rows,1):
            replies = [s[i] for s in sources]
            require(all("result" in r for r in replies),f"code unavailable at rank {row['rank']}")
            code = replies[0]["result"]
            require(all(r["result"]==code for r in replies),"independent archive code mismatch")
            require(isinstance(code,str) and re.fullmatch(r"0x(?:[a-f0-9]{2})*",code),
                    "invalid contract code bytes")
            data = bytes.fromhex(code[2:])
            kind = "delegated_code" if len(data)==23 and data[:3]==b"\xef\x01\x00" else (
                   "deployed_code" if data else "empty_code")
            value = {**row,"code_status_at_period_end":kind,"code_bytes":len(data),
                     "code_sha256":sha256(data).hexdigest(),
                     "delegation_target":"0x"+data[3:].hex() if kind=="delegated_code" else "none"}
            checked.append(value)
            if data:
                selected.append(value)
        if len(selected)>=20:
            break
    require(len(selected)>=20, "not enough known code-bearing addresses to certify top 20")
    cols = list(checked[0])
    csv_out(packet/"checked-recipient-code.tsv",cols,([x[c]for c in cols] for x in checked))
    csv_out(packet/"top20-code-recipients.tsv",["contract_rank",*cols],
            ([i,*(x[c]for c in cols)] for i,x in enumerate(selected[:20],1)))
    (packet/"contract-rank-validation.json").write_text(json.dumps(dict(
        code_block=last,code_block_hash=block["hash"],checked_top_recipient_prefix=len(checked),
        code_nonempty_in_prefix=len(selected),ranked_contract_count=20,
        ranking_is_complete_under_filter=True,
        archive_endpoints=[url for _,url in ARCHIVES], all_code_bytes_matched=True,
        metric="sum(receipt_gas_used) per top-level recipient over full day; retain nonempty end-of-day code",
        exact_scope="reverts and nested gas included in payer receipt; direct recipient only; creations separate",
    ),indent=2)+"\n")
    print("Complete top 20 nonempty-code recipients at block",last,
          "from first",len(checked),"global ranks")


def check_packet(packet):
    manifest = json.loads((packet/"manifest.json").read_text())
    for r in manifest["files"]:
        p = packet/r["file"]
        require(p.stat().st_size==r["bytes"] and sha256(p.read_bytes()).hexdigest()==r["sha256"],
                "packet byte/hash mismatch: "+r["file"])
    a = json.loads((packet/"aggregation.json").read_text())
    chunks = json.loads((packet/"chunk-requests.json").read_text())
    expected_rows = {"blocks":a["block_count"],"transactions":a["transactions"]}
    for table, names in (("blocks",BLOCK_COLUMNS),("transactions",TX_COLUMNS)):
        raw, meta = footer((packet/f"{table}-tail.bin").read_bytes())
        require(meta[3]==expected_rows[table] and raw==(packet/f"{table}-footer.bin").read_bytes(),
                "footer row count/bytes disagree")
        obj = list_object(packet,table)
        plan = range_plan(meta,names)
        observed = [r for r in chunks if r["table"]==table]
        for want, got in zip(plan,observed,strict=True):
            start, n = want["start"], want["length"]
            require(all(got[k]==v for k,v in want.items()) and got["url"]==AWS+obj["Key"]
                    and got["status"]==206 and got["response_headers"]["ETag"]==obj["ETag"]
                    and got["response_headers"]["Content-Range"]==f"bytes {start}-{start+n-1}/{obj['Size']}",
                    "range provenance disagrees with exact partition plan")
    top = tab(packet/"top100-recipients.tsv")
    addresses = set()
    sums = [0,0,0]
    last = None
    with gzip.open(packet/"all-recipients.tsv.gz","rt",newline="") as f:
        for i,row in enumerate(csv.DictReader(f,delimiter="\t"),1):
            address = row["recipient"]
            gas,n,reverts = (int(row[k])for k in ("receipt_gas_used","transactions","reverted_transactions"))
            key = -gas,address
            require(i==int(row["rank"]) and re.fullmatch(r"0x[0-9a-f]{40}",address) and
                    address not in addresses and 0<gas and 0<=reverts<=n and n>0 and
                    (last is None or last<key), "invalid recipient row/order")
            if i<=100:
                require(row==top[i-1],"top slice disagrees with complete rank")
            addresses.add(address)
            sums[0]+=gas
            sums[1]+=n
            sums[2]+=reverts
            last=key
    require(len(addresses)==a["distinct_nonnull_recipients"] and
            sums[0]+a["contract_creation_gas"]==a["total_header_gas"]==a["total_receipt_gas"] and
            sums[1]+a["contract_creation_transactions"]==a["transactions"] and
            sums[2]+a["reverted_contract_creations"]==a["reverted_transactions"],
            "recipient aggregate does not reconcile with full day")
    checked = tab(packet/"checked-recipient-code.tsv")
    selected = tab(packet/"top20-code-recipients.tsv")
    code_state = json.loads((packet/"contract-rank-validation.json").read_text())
    require(len(checked)==code_state["checked_top_recipient_prefix"] and len(checked)<=len(top),
            "wrong count of code-checked rows")
    for row,root in zip(checked,top[:len(checked)],strict=True):
        require(all(row[k]==v for k,v in root.items()), "code checks do not cover a top-ranked prefix")
    for offset in range(0,len(checked),20):
        rows = checked[offset:offset+20]
        for name,url in ARCHIVES:
            tag = f"archive-{name}-code-{offset+1:03}"
            req = json.loads((packet/f"rpc-{tag}-request.json").read_text())
            reply = {v["id"]:v["result"] for v in json.loads((packet/f"rpc-{tag}-response.json").read_text())}
            prov = json.loads((packet/f"rpc-{tag}-provenance.json").read_text())
            require(prov["url"]==url and reply[1]=="0x1" and len(req)==len(reply)==len(rows)+1,
                    "archive data chain or row-count mismatch")
            for i,row in enumerate(rows,2):
                require(req[i-1]["params"]==[row["recipient"],{"blockHash":code_state["code_block_hash"],
                                                              "requireCanonical":True}],
                        "archive query differs from fixed recipient and block")
                code = bytes.fromhex(reply[i][2:])
                require(len(code)==int(row["code_bytes"]) and sha256(code).hexdigest()==row["code_sha256"],
                        "archive code mismatch")
    expected = [row for row in checked if row["code_status_at_period_end"]!="empty_code"][:20]
    require(len(expected)==len(selected)==20, "missing complete top-20 rank")
    for i,(a_row, b_row) in enumerate(zip(expected,selected,strict=True),1):
        require(b_row=={"contract_rank":str(i),**a_row},"top-20 code table does not match checked rank")
    triage = tab(packet/"utxo-triage.tsv")
    require(len(triage)==20 and all(a_row["recipient"]==b_row["recipient"] for a_row,b_row in zip(selected,triage,strict=True)),
            "missing or mismatched UTXO verdict")
    print(len(addresses),"ordered recipients, all gas/counts, and all 20 published ranked rows reconciled")


if __name__ == "__main__":
    p = ArgumentParser()
    p.add_argument("packet", type=Path)
    p.add_argument("--fetch-ranges", action="store_true")
    p.add_argument("--rank", action="store_true")
    p.add_argument("--verify-rpc", action="store_true")
    p.add_argument("--rank-contracts", action="store_true")
    p.add_argument("--check", action="store_true")
    a = p.parse_args()
    if a.check:
        check_packet(a.packet)
    else:
        inspect(a.packet)
    if a.fetch_ranges:
        fetch_ranges(a.packet)
    if a.rank:
        rank_period(a.packet)
    if a.verify_rpc:
        verify_rpc(a.packet)
    if a.rank_contracts:
        rank_contracts(a.packet)
