"""Read-only isolated extension review; not a replacement for full acceptance."""
import argparse
import hashlib
import json
import re
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument("--baseline", type=Path, required=True)
p.add_argument("--candidate", type=Path, required=True)
p.add_argument("--preliminary", type=Path, required=True)
a = p.parse_args()
here = Path(__file__).resolve().parent

def rows(name):
    return [line.split() for line in (here / name).read_text().splitlines()
            if line.strip() and not line.startswith("#")]

results = rows("public-theorems.txt.source")
definitions = rows("contract-definitions.txt.source")
base = (a.baseline / "C/jet_contracts.expected").read_text()
current = (a.candidate / "C/jet_contracts.expected").read_text()
# All baseline theorem types precede all baseline definitions. The only two
# permitted insertions are the complete new theorem group and definition group.
first = current.index(results[0][1] + "\n")
end = current.index(definitions[0][1] + " =")
prefix = base[:first]
assert current.startswith(prefix)
suffix = base[first:]
assert current[:end].endswith(suffix)
types = current[first:end-len(suffix)]
defs = current[end:]
assert current == prefix + types + suffix + defs

preliminary = (a.preliminary / "contracts-review.out").read_text()

def normalize(s):
    # Supplemental textual correspondence only; kernel types and source
    # correspondence are checked independently, with their actual namespaces.
    return re.sub(r"\s+", "", re.sub(
        r"(?:[A-Za-z_][A-Za-z_0-9]*\.)+([A-Za-z_][A-Za-z_0-9]*)", r"\1", s))

def type_records(s):
    names = "|".join(re.escape(n) for _, n in results)
    return {m.group(1): m.group(0).strip() for m in re.finditer(
        r"(?m)^(" + names + r")\n(?:(?!^[A-Za-z_]).*\n)*", s)}

x, y = type_records(types), type_records(preliminary)
assert len(x) == len(y) == len(results) == 71
assert all(normalize(x[n]) == normalize(y[n]) for _, n in results)

def definition_records(s):
    names = "|".join(re.escape(n) for _, n in definitions)
    return {n: re.search(
        r"(?ms)^" + re.escape(n) + r" =.*?(?=^(?:" + names + r") =|\Z)",
        s).group(0).strip() for _, n in definitions}

x, y = definition_records(defs), definition_records(preliminary)
exceptions = {n for _, n in definitions if normalize(x[n]) != normalize(y[n])}
assert len(x) == len(y) == len(definitions) == 22
assert exceptions == {"point_write_run", "point_write_tree"}
# Standard depth truncates generated computations. Preserve its settings,
# supplement with deep prints and the kernel-checked run equality, and require
# exact source hashes rather than pretending to compare truncated trace nodes.
assembly = json.loads((here / "ASSEMBLY.json").read_text())
for record in assembly["sources"]:
    path = a.candidate / record["path"]
    assert hashlib.sha256(path.read_bytes()).hexdigest() == record["sha256"]

def assumption_records(path):
    result = {}
    for line in path.read_text().splitlines():
        name, axioms = line.split(" : ", 1)
        assert name not in result
        result[name] = axioms
    return result

old = assumption_records(a.baseline / "C/jet_assumptions.expected")
now = assumption_records(a.candidate / "C/jet_assumptions.expected")
new = assumption_records(here / "assumptions-provisional.expected.source")
assert set(new) == {m + "." + n for m, n in results}
assert not (set(old) & set(new))
assert now == old | new
print(json.dumps({
    "old_contract_lines": len(base.splitlines()),
    "new_type_lines": len(types.splitlines()),
    "new_definition_lines": len(defs.splitlines()),
    "reviewed_types": len(results),
    "reviewed_definitions": len(definitions),
    "deep_print_supplements": sorted(exceptions),
    "assumptions": len(now),
    "closed": sum(v == "closed" for v in now.values()),
    "old_records_unchanged": len(old),
    "contract_sha256": hashlib.sha256(current.encode()).hexdigest(),
    "assumptions_sha256": hashlib.sha256(
        (a.candidate / "C/jet_assumptions.expected").read_bytes()).hexdigest(),
}, indent=2))
