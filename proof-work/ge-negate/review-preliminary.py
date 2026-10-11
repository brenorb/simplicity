"""Read-only preliminary audit; no expected snapshots or proof inputs edited.

Ellipsis diagnostics compare retained text only, not omitted-term equality.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, re, sys
sys.dont_write_bytecode=True

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rows(p):
    r=[l.split() for l in p.read_text().splitlines() if l.strip() and not l.startswith('#')]
    if any(len(x)!=2 for x in r) or len({'.'.join(x) for x in r})!=len(r):
        raise ValueError('malformed/duplicate inventory')
    return r
def norm(s):return re.sub(r'\s+','',s)
def retained(a,b):
    pos=0;b=norm(b)
    for i,x in enumerate(norm(a).split('...')):
        at=b.find(x,pos)
        if at<0 or (i==0 and at!=0):return False
        pos=at+len(x)
    return pos==len(b)
def types(s,rs):
    names='|'.join(re.escape(n) for _,n in rs)
    ms=list(re.finditer(r'(?m)^@?('+names+r')(?:[ \t]+\?\w+)*\n(?:(?!^[@A-Za-z_]).*\n)*',s))
    if len(ms)!=len(rs) or len({m[1] for m in ms})!=len(rs):
        raise ValueError('missing/duplicate printed type')
    return {m[1]:m[0].strip() for m in ms}
def definitions(s,ds):
    names='|'.join(re.escape(n) for _,n in ds)
    pattern=r'(?m)^(?:(?:Variant|Record|Inductive) )?('+names+r')(?= =| :)'
    ms=list(re.finditer(pattern,s))
    if len(ms)!=len(ds) or len({m[1] for m in ms})!=len(ds):
        raise ValueError('missing/duplicate printed definition')
    return {m[1]:s[m.start():ms[i+1].start() if i+1<len(ms) else len(s)].strip()
            for i,m in enumerate(ms)}

def review(archive,work):
    rs=rows(archive/'public-results.txt.source');ds=rows(archive/'contract-definitions.txt.source')
    if len(rs)!=109 or len(ds)!=37:raise ValueError('unexpected inventory size')
    for f in json.loads((archive/'manifest.json').read_text())['files']:
        if sha(archive/f['path'])!=f['sha256']:raise ValueError('archive hash '+f['path'])
        if f['materialized_name'].endswith('.v'):
            if sha(work/f['materialized_name'])!=f['sha256']:raise ValueError('materialized proof hash '+f['path'])
    for name in ['contracts-standard.err','contracts-review.err','assumptions-109-review.err']:
        if (work/name).read_text():raise ValueError('nonempty diagnostics '+name)
    a=(work/'contracts-standard.out').read_text();b=(work/'contracts-review.out').read_text()
    if '...' in b:raise ValueError('deep report still truncated')
    report={}
    expected={'types':{'eval_owned_read_fe'},
              'definitions':{'affine_weak_run','affine_weak_tree','affine_negate_run',
                             'affine_negate_tree','owned_read_run','owned_read_tree',
                             'owned_write_run','owned_write_tree'}}
    for label,parse,inventory in [('types',types,rs),('definitions',definitions,ds)]:
        x,y=parse(a,inventory),parse(b,inventory)
        changed={n for n in x if norm(x[n])!=norm(y[n])}
        if changed!=expected[label]:raise ValueError('unexpected print-depth differences '+label)
        for n in changed:
            if '...' not in x[n] or not retained(x[n],y[n]):raise ValueError('non-ellipsis difference '+n)
        report[label]={'count':len(x),'exact_whitespace_normalized':len(x)-len(changed),
                       'deep_supplements':sorted(changed)}
    spec=importlib.util.spec_from_file_location('parser',archive.parent/'gej-predicate/review-preliminary.py')
    parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
    assumptions=parser.assumptions(work/'assumptions-109-review.out',{'.'.join(r) for r in rs})
    return {'contracts':report,'assumptions':{k:sorted(v) for k,v in sorted(assumptions.items())},
            'results':len(assumptions),'closed':sum(not v for v in assumptions.values()),
            'axiom_union':sorted(set().union(*assumptions.values())),
            'output_hashes':{n:sha(work/n) for n in ['contracts-standard.out','contracts-review.out','assumptions-109-review.out']},
            'full_acceptance':False}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--archive',type=Path,required=True);p.add_argument('--work',type=Path,required=True)
    a=p.parse_args();print(json.dumps(review(a.archive,a.work),indent=2))
