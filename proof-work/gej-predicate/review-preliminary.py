"""Read-only preliminary predicate audit, not isolated full acceptance.

Compare ordinary-depth contracts with deep supplements. Ellipsis comparisons
only check retained text in order; they are not structural proof-term equality.
Parse actual Print Assumptions with strict markers and inherited-axiom checks.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def rows(path):
    result = [line.split() for line in path.read_text().splitlines()
              if line.strip() and not line.startswith('#')]
    if any(len(r) != 2 for r in result): raise ValueError('malformed inventory')
    if len({'.'.join(r) for r in result}) != len(result): raise ValueError('duplicate inventory')
    return result

def normalize(s):
    return re.sub(r'\s+', '', s)

def retained_fragments(standard, deep):
    # A supplemental printing diagnostic, not an equality certificate.
    parts = normalize(standard).split('...')
    actual = normalize(deep)
    pos = 0
    for i, part in enumerate(parts):
        at = actual.find(part, pos)
        if at < 0 or (i == 0 and at != 0): return False
        pos = at + len(part)
    return pos == len(actual)

def contract_review(here, work):
    results = rows(here/'public-results.txt.source')
    definitions = rows(here/'contract-definitions.txt.source')
    ordinary = (work/'contracts-standard.out').read_text()
    deep = (work/'contracts-review.out').read_text()
    if '...' in deep: raise ValueError('deep supplement still truncated')
    for name in ['contracts-standard.err','contracts-review.err']:
        p = work/name
        if p.exists() and p.read_text(): raise ValueError('nonempty diagnostics '+name)
    def types(s):
        names = '|'.join(re.escape(n) for _,n in results)
        matches = list(re.finditer(r'(?m)^('+names+r')\n(?:(?!^[A-Za-z_]).*\n)*',s))
        if len(matches) != len(results): raise ValueError('missing/duplicate printed types')
        return {m[1]:m[0].strip() for m in matches}
    def defs(s):
        names = '|'.join(re.escape(n) for _,n in definitions)
        matches = list(re.finditer(r'(?ms)^('+names+r') =.*?(?=^(?:'+names+r') =|\Z)',s))
        if len(matches) != len(definitions): raise ValueError('missing/duplicate printed definitions')
        return {m[1]:m[0].strip() for m in matches}
    report = {}
    expected = {'types':{'eval_point_read_fe','eval_point_three_readers'},
                'definitions':{'point_read_run','point_read_tree','point_zero_run','point_zero_ret'}}
    for label, parse in [('types',types),('definitions',defs)]:
        x,y = parse(ordinary),parse(deep)
        differences = {n for n in x if normalize(x[n]) != normalize(y[n])}
        if differences != expected[label]: raise ValueError('unexpected print differences '+label)
        for n in differences:
            if '...' not in x[n] or not retained_fragments(x[n],y[n]):
                raise ValueError('non-ellipsis change '+n)
        report[label] = {'count':len(x),'exact_whitespace_normalized':len(x)-len(differences),
                         'deep_supplements':sorted(differences)}
    return report

INHERITED = {
 'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep',
 'ClassicalDedekindReals.sig_forall_dec','ClassicalDedekindReals.sig_not_dec',
 'Events.external_functions_sem','Events.external_functions_properties',
 'Events.inline_assembly_sem','Events.inline_assembly_properties'}

def assumptions(path, wanted):
    result, current, mode = {}, None, None
    def finish():
        if current is not None and mode is None:
            raise ValueError('unfinished report '+current)
        if current is not None and mode == 'axioms' and not result[current]:
            raise ValueError('empty axiom section '+current)
    for line in path.read_text().splitlines():
        m = re.fullmatch(r'JET_ASSUMPTIONS (\S+)',line)
        if m:
            finish(); current = m[1]
            if current in result: raise ValueError('duplicate marker '+current)
            result[current] = set(); mode = None
        elif line == 'Axioms:':
            if current is None or mode is not None: raise ValueError('unexpected axiom section')
            mode = 'axioms'
        elif line.startswith('Closed under the global context'):
            if current is None or mode is not None: raise ValueError('unexpected closed section')
            mode = 'closed'
        elif mode == 'axioms' and line and not line[0].isspace():
            result[current].add(line.split()[0])
    finish()
    if set(result) != wanted: raise ValueError('missing/extra theorem markers')
    unexpected = set().union(*result.values()) - INHERITED
    if unexpected: raise ValueError('unexpected axioms '+repr(sorted(unexpected)))
    return result

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--work',type=Path,required=True)
    p.add_argument('--archive',type=Path,default=Path(__file__).resolve().parent)
    p.add_argument('--assumptions',action='store_true')
    a = p.parse_args()
    manifest = json.loads((a.archive/'manifest.json').read_text())
    for record in manifest['files']:
        if sha(a.archive/record['path']) != record['sha256']:
            raise ValueError('archive hash mismatch '+record['path'])
        if record['materialized_name'].endswith('.v'):
            if sha(a.work/record['materialized_name']) != record['sha256']:
                raise ValueError('compiled candidate source mismatch '+record['path'])
    report = {'contracts':contract_review(a.archive,a.work),
              'standard_contract_sha256':sha(a.work/'contracts-standard.out'),
              'deep_contract_sha256':sha(a.work/'contracts-review.out'),
              'full_acceptance':False}
    if a.assumptions:
        err = a.work/'assumptions-review.err'
        if err.read_text(): raise ValueError('assumption diagnostics not empty')
        wanted = {'.'.join(r) for r in rows(a.archive/'public-results.txt.source')}
        actual = assumptions(a.work/'assumptions-review.out',wanted)
        report['assumptions'] = {n:sorted(v) for n,v in sorted(actual.items())}
        report['assumption_results'] = len(actual)
        report['closed'] = sum(not v for v in actual.values())
        report['assumptions_output_sha256'] = sha(a.work/'assumptions-review.out')
    print(json.dumps(report,indent=2))
