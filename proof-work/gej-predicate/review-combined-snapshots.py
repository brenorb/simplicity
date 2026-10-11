"""Read-only exact inherited-record reconciliation, not acceptance."""
from pathlib import Path
import re, json, hashlib, difflib
base=Path('/tmp/jet-add-accept.qwqWy1/Coq/C')
cand=Path('/tmp/jet-predicate-accept.EX7adj/Coq/C')
repo=Path('/Users/brenorb/code/PROJECTS/BLOCKSTREAM/simplicity')
def rows(p):
    return [tuple(l.split()) for l in p.read_text().splitlines() if l.strip() and not l.startswith('#')]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
old=rows(base/'jet_public_theorems.txt');new=rows(cand/'jet_public_theorems.txt')
od=rows(base/'jet_contract_definitions.txt');nd=rows(cand/'jet_contract_definitions.txt')
assert new[:len(old)]==old and nd[:len(od)]==od
added=new[len(old):];defs=nd[len(od):]
assert len(added)==133 and len(defs)==43
names={n for _,n in added+defs};allnames={n for _,n in new+nd}
assert not names & {n for _,n in old+od}
def chunks(s):
    pattern=r'(?m)^(@?(?:[A-Za-z_][\w\']*\.)*(?:'+ '|'.join(map(re.escape,sorted(allnames,key=len,reverse=True)))+r'))(?=(?:[ \t]*=[ \t]*|(?:[ \t]+\?[\w]+)*)$)'
    matches=list(re.finditer(pattern,s));result=[]
    for i,m in enumerate(matches):
        n=m[1].lstrip('@').split('.')[-1]
        result.append((n,s[m.start():matches[i+1].start() if i+1<len(matches) else len(s)]))
    assert matches and matches[0].start()==0
    return result
actual=chunks((cand/'jet_contracts.expected').read_text())
counts={n:sum(k==n for k,_ in actual) for n in names}
assert set(counts.values())=={1},counts
inherited=''.join(s for n,s in actual if n not in names)
baseline=(base/'jet_contracts.expected').read_text()
if inherited!=baseline:
    print('Inherited contracts differ:')
    print(''.join(list(difflib.unified_diff(baseline.splitlines(True),inherited.splitlines(True)))[:100]))
    raise SystemExit(1)
def asm(p):
    lines=[l for l in p.read_text().splitlines() if l.strip()]
    r=dict(l.split(' : ',1) for l in lines)
    assert len(r)==len(lines)
    return r
a,b=asm(base/'jet_assumptions.expected'),asm(cand/'jet_assumptions.expected')
assert all(b.get(k)==v for k,v in a.items())
assert set(b)-set(a)=={'.'.join(r) for r in added}
for group,file in [('gej-infinity','assumptions-provisional.expected.source'),('gej-predicate','assumptions-provisional.expected.source')]:
    expected=asm(repo/'proof-work'/group/file)
    assert all(b.get(k)==v for k,v in expected.items()),group
# Preliminary print contexts must agree; ellipses are a diagnostic, not equality.
def norm(s):
    # A global's qualification changes with the imported printing context.
    modules={'jet_frame_inv','jet_frame_layout','jet_output_layout','jet_secp_fe_nv',
      'jet_secp_frame','jet_secp_linkage','jet_secp_local_regions','jet_secp_normalize_local',
      'jet_secp_public_body','jet_secp_public_copy','jet_secp_write_fe_wide_exec',
      'jet_secp_write_fe_wide_values','jet_secp_write_fe_wrapper','jet_sx_eval',
      'jet_sx_exec','jet_sx_expr','jet_sx_mem','jet_sx_rep','jet_sx_state',
      'jet_secp_point_write_run','jet_encoding','jet_input_layout','jet_readBit_layout',
      'jet_secp_b32_exec','jet_secp_canonical_normalize','jet_secp_canonical_zero',
      'jet_secp_fe_math','jet_secp_field_zero','jet_secp_fns','jet_secp_gej_public_entry',
      'jet_secp_odd_body','jet_secp_read_fe_numeric','jet_secp_wrapper_run',
      'jet_secp_write_fe_numeric','jet_sx_pure','jet_sx_zrep','jet_sx_zval'}
    s=re.sub(r'\b('+'|'.join(map(re.escape,sorted(modules)))+r')\.([A-Za-z_][\w]*)',r'\2',s)
    s=s.replace('jets.f_writeBit','f_writeBit')
    return re.sub(r'\s+','',s)
reports={}
for group,work,source in [('gej-infinity','/tmp/jet-gej-infinity.YrUC7w','contracts-review.out'),
                          ('gej-predicate','/tmp/jet-gej-predicate.W2FtCz','contracts-standard.out')]:
    expected=dict(chunks((Path(work)/source).read_text()))
    groupnames={n for _,n in added+defs if (repo/'proof-work'/group).joinpath('manifest.json').exists()
                and n in expected}
    mismatches=[]
    for n,s in actual:
        if n not in groupnames:continue
        x,y=norm(s),norm(expected[n])
        if x!=y:
            parts=x.split('...');pos=0
            for i,p in enumerate(parts):
                at=y.find(p,pos)
                if at<0 or (i==0 and at!=0):break
                pos=at+len(p)
            else:
                if pos==len(y) and '...' in x:
                    mismatches.append(n);continue
            print('Unexpected preliminary context difference',group,n)
            print(''.join(difflib.unified_diff(s.splitlines(True),expected[n].splitlines(True)))[:3500]);raise SystemExit(1)
    reports[group]={'records':len(groupnames),'deep_ellipsis_supplements':mismatches}
print(json.dumps({'inherited_contracts_byte_identical':True,'inherited_assumptions_identical':len(a),
 'added_results':len(added),'added_definitions':len(defs),'new_assumptions_match_preliminary':True,
 'preliminary_contract_comparisons':reports,
 'candidate_snapshots':{n:sha(cand/n) for n in ['jet_contracts.expected','jet_assumptions.expected']},
 'full_acceptance':False},indent=2))
