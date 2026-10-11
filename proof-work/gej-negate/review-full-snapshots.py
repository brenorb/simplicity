"""Read-only exact inherited-record reconciliation, not acceptance."""
from pathlib import Path
import re, json, hashlib, difflib
base=Path('/tmp/jet-predicate-accept.EX7adj/Coq/C')
cand=Path('/tmp/jet-gej-negate-accept.5ZRUlU/Coq/C')
repo=Path('/Users/brenorb/code/PROJECTS/BLOCKSTREAM/simplicity')
def rows(p):
    return [tuple(l.split()) for l in p.read_text().splitlines() if l.strip() and not l.startswith('#')]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
archive=repo/'proof-work/gej-negate'
assembly=json.loads((archive/'ASSEMBLY.json').read_text())
for item in assembly['files']:
    assert sha(cand.parent/item['path'])==item['candidate_sha256'],item['path']
inherited_sources=list(base.glob('*.v'))
assert len(inherited_sources)==889
for p in inherited_sources:
    assert (cand/p.name).read_bytes()==p.read_bytes(),p.name
source_manifest=json.loads((archive/'manifest.json').read_text())
new_sources=0
for item in source_manifest['files']:
    if item['materialized_name'].endswith('.v'):
        assert sha(cand/item['materialized_name'])==item['sha256'],item['path']
        assert sha(archive/item['path'])==item['sha256'],item['path']
        new_sources+=1
assert new_sources==34
old=rows(base/'jet_public_theorems.txt');new=rows(cand/'jet_public_theorems.txt')
od=rows(base/'jet_contract_definitions.txt');nd=rows(cand/'jet_contract_definitions.txt')
assert new[:len(old)]==old and nd[:len(od)]==od
added=new[len(old):];defs=nd[len(od):]
assert len(added)==80 and len(defs)==26
names={n for _,n in added+defs};allnames={n for _,n in new+nd}
assert not names & {n for _,n in old+od}
def chunks(s):
    pattern=r'(?m)^(?:(?:Variant|Record) )?(@?(?:[A-Za-z_][\w\']*\.)*(?:'+ '|'.join(map(re.escape,sorted(allnames,key=len,reverse=True)))+r'))(?=(?:[ \t]*[:=]|(?:[ \t]+\?[\w]+)*\n[ \t]+:))'
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
for group,file in [('gej-negate','assumptions-provisional.expected.source')]:
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
      'jet_secp_write_fe_numeric','jet_sx_pure','jet_sx_zrep','jet_sx_zval',
      'jet_secp_point_write_field','jet_secp_gej_negate_literal','jet_secp_gej_negate_boundary',
      'jet_secp_point_negate_exec','jet_secp_point_weak_exec','jet_secp_point_weak_values',
      'jet_secp_gej_infinity_layout','jet_secp_point_read_run','jet_secp_point_weak_owned',
      'jet_secp_point_negate_owned','jet_secp_point_write_general_preservation',
      'jet_secp_read_gej_fields','jet_secp_write_gej_negated_literal','jet_secp_point_three_reads',
      'jet_secp_field_negate_storage','jet_secp_field_negate_values','jet_secp_negate_literal_contract',
      'jet_secp_canonical_negate','jet_toZ','jet_word_repr',
      'jet_secp_gej_predicate_body','jet_secp_gej_public_body'}
    s=re.sub(r'\b('+'|'.join(map(re.escape,sorted(modules)))+r')\.([A-Za-z_][\w]*)',r'\2',s)
    s=s.replace('jets.f_writeBit','f_writeBit')
    return re.sub(r'\s+','',s)
reports={}
for group,work,source in [('gej-negate','/tmp/jet-gej-negate.IMImaX','contracts-review.out')]:
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
            mismatch=next((i for i,(u,v) in enumerate(zip(x,y)) if u!=v), min(len(x),len(y)))
            print('First normalized difference:',x[max(0,mismatch-80):mismatch+300],
                  y[max(0,mismatch-80):mismatch+300])
            print(''.join(difflib.unified_diff(s.splitlines(True),expected[n].splitlines(True)))[:3500]);raise SystemExit(1)
    reports[group]={'records':len(groupnames),'deep_ellipsis_supplements':mismatches}
assert reports['gej-negate']['records']==106
assert set(reports['gej-negate']['deep_ellipsis_supplements'])=={
    'exec_gej_negate_prefix_framed','exec_gej_negate_owned_prefix',
    'point_negate_run','point_negate_tree','point_weak_bounds','point_weak_math',
    'point_weak_run','point_weak_tree'}
print(json.dumps({'inherited_contracts_byte_identical':True,'inherited_assumptions_identical':len(a),
 'candidate':str(cand.parent.parent),'inherited_sources_byte_identical':len(inherited_sources),
 'archived_new_proofs_hash_identical':new_sources,'assembly_metadata_hash_identical':len(assembly['files']),
 'added_results':len(added),'added_definitions':len(defs),'new_assumptions_match_preliminary':True,
 'preliminary_contract_comparisons':reports,
 'candidate_snapshots':{n:sha(cand/n) for n in ['jet_contracts.expected','jet_assumptions.expected']},
 'full_acceptance':False},indent=2))

