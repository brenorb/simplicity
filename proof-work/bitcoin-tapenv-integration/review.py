"""Review/import frozen taproot-builder support, preserving main's program."""
import argparse
import importlib.util
import json
from pathlib import Path
import re
import subprocess

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('tapenv_check',HERE/'check.py')
audit=importlib.util.module_from_spec(spec);spec.loader.exec_module(audit)
stage=audit.stage


def review(work):
    meta=json.loads((work/'ASSEMBLY.json').read_text());receipt=json.loads((work/'REVIEW.json').read_text())
    if (Path(meta['candidate']).resolve()!=work.resolve() or meta['source_commit']!=stage.COMMIT
            or receipt['source_commit']!=stage.COMMIT or receipt['normal_registration'] or receipt['coverage_added']):
        raise ValueError('builder scope/identity drift')
    for field,stem in [('AST','ast'),('build','build'),('assumptions_check','assumptions'),('contract_check','contracts'),('kernel','kernel')]:
        evidence=receipt[field]
        if evidence['exit_code'] or evidence['log_sha256']!=stage.patch.sha((work/(stem+'.log')).read_bytes()):raise ValueError('nonterminal/changed evidence')
    changes={};results=[];definitions=[]
    for e in meta['modules']:
        raw=stage.blob(e['origin'])
        if stage.patch.sha(raw)!=e['sha256'] or (work/'Coq/C'/(e['name']+'.v')).read_bytes()!=raw:raise ValueError('frozen source drift')
        if e['origin'].startswith('Coq/bitcoin-env/'):
            target=stage.REPO/e['origin']
            if target.exists() and target.read_bytes()!=raw:raise ValueError('builder source collision')
            changes[target]=raw.decode()
            results+=['C.'+e['name']+'.'+n for n in e['results']]
            definitions+=['C.'+e['name']+'.'+n for n in e['definitions']]
    for path,value in meta['inherited_sha256'].items():
        if stage.patch.sha((stage.REPO/path).read_bytes())!=value:raise ValueError('inherited source changed')
    for name in ['jets_bitcoin_env.v','jet_bitcoin_env_translation_unit.c','regenerate-bitcoin-env.sh']:
        path='Coq/C/'+name;raw=stage.blob(path)
        if (work/path).read_bytes()!=raw:raise ValueError('program/input provenance drift')
        target=stage.REPO/path
        if target.exists() and target.read_bytes()!=raw:raise ValueError('program source collision')
        changes[target]=raw.decode()
    if (work/'regenerated.v').read_bytes()!=(work/'Coq/C/jets_bitcoin_env.v').read_bytes():raise ValueError('generated production AST mismatch')
    deps=audit.normal.assumptions((work/'assumptions.log').read_text())
    if set(deps)!=set(results) or {n:sorted(ds) for n,ds in deps.items()}!=receipt['expected_dependencies']:raise ValueError('dependency inventory mismatch')
    text=(work/'contracts.log').read_text()
    if '...' in text or re.findall(r'(?m)^TAPENV_(TYPE|DEF) (\S+)$',text)!=[('TYPE',n) for n in results]+[('DEF',n) for n in definitions]:raise ValueError('deep record inventory mismatch')
    audit.kernel.kernel((work/'kernel.log').read_text(),sorted((stage.REPO/'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    return {'candidate':str(work),'builder_modules':len(changes)-3,'results':len(results),'definitions':len(definitions),
            'fresh_kernel_checked':True,'actual_production_AST_regenerated':True,'normal_registration':False,
            'coverage_added':0,'main_installation':False,'boundaries':receipt['explicit_boundaries']},changes


def install(work):
    result,changes=review(work)
    before=stage.patch.sha(subprocess.check_output(['git','diff','--cached','--binary'],cwd=stage.REPO))
    old={str(p.relative_to(stage.REPO)):stage.patch.sha(p.read_bytes()) for p in (stage.REPO/'Coq').rglob('*.v')}
    stage.patch.patch_files({p:text for p,text in changes.items() if not p.exists()})
    for path,value in old.items():
        if stage.patch.sha((stage.REPO/path).read_bytes())!=value:raise ValueError('existing proof overwritten')
    if stage.patch.sha(subprocess.check_output(['git','diff','--cached','--binary'],cwd=stage.REPO))!=before:raise ValueError('original index changed')
    result.update(main_installation=True,preexisting_staged_patch_sha256=before)
    return result


if __name__=='__main__':
    cli=argparse.ArgumentParser();cli.add_argument('--candidate',type=Path,required=True);cli.add_argument('--install',action='store_true')
    args=cli.parse_args();work=args.candidate.resolve()
    print(json.dumps(install(work) if args.install else review(work)[0],indent=2))
