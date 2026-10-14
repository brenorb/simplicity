"""Fresh derived-program builder audit; no main sources or registries written."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('tapenv_stage',HERE/'stage.py')
stage=importlib.util.module_from_spec(spec);spec.loader.exec_module(stage)
spec=importlib.util.spec_from_file_location('tapenv_reports',HERE.parent/'scalar-multiply-integration/review-normal.py')
normal=importlib.util.module_from_spec(spec);spec.loader.exec_module(normal)
spec=importlib.util.spec_from_file_location('tapenv_kernel',HERE.parent/'scalar-mul/review.py')
kernel=importlib.util.module_from_spec(spec);spec.loader.exec_module(kernel)
ENV=dict(os.environ,PATH='/nix/store/57myhb98wx8k9dr21cf51bsmvxjs67h6-coq-8.17.1/bin:'+os.environ['PATH'],PYTHONDONTWRITEBYTECODE='1',
         COMPCERT='/Users/brenorb/.cache/simplicity-jet-deps/compcert-3.14',JET_SYSROOT='/Users/brenorb/.cache/simplicity-jet-deps/sysroot-glibc-2.36')


def run(work,cmd,stem,timeout):
    with (work/(stem+'.log')).open('wb') as log:
        done=subprocess.run(cmd,cwd=work/'Coq',env=ENV,stdout=log,stderr=subprocess.STDOUT,timeout=timeout)
    if done.returncode:raise ValueError('failed '+stem+'; inspect retained log')
    return {'exit_code':done.returncode,'log_sha256':stage.patch.sha((work/(stem+'.log')).read_bytes()),'command':cmd}


def check(work):
    meta=json.loads((work/'ASSEMBLY.json').read_text())
    for e in meta['modules']:
        if stage.patch.sha((work/'Coq/C'/(e['name']+'.v')).read_bytes())!=e['sha256']:raise ValueError('source drift')
    ast=run(work,['bash','C/regenerate-bitcoin-env.sh',str(work/'regenerated.v')],'ast',120)
    if (work/'regenerated.v').read_bytes()!=(work/'Coq/C/jets_sha.v').read_bytes():raise ValueError('AST not actual production unit')
    build=run(work,['bash','build-jets.sh','-j2'],'build',5400)
    entries=[e for e in meta['modules'] if e['origin'].startswith('Coq/bitcoin-env/')]
    results=['C.'+e['name']+'.'+n for e in entries for n in e['results']]
    definitions=['C.'+e['name']+'.'+n for e in entries for n in e['definitions']]
    prefix=['Set Warnings "-notation-overridden".']+['Require C.'+e['name']+'.' for e in entries]
    assumptions=prefix[:]
    for n in results:assumptions+=['Goal True. idtac "JET_ASSUMPTIONS '+n+'". exact I. Qed.','Print Assumptions '+n+'.']
    driver=prefix+['Set Printing All.','Set Printing Width 120.','Set Printing Depth 1000000.']
    wanted=[('TYPE',n) for n in results]+[('DEF',n) for n in definitions]
    for kind,n in wanted:driver+=['Goal True. idtac "TAPENV_'+kind+' '+n+'". exact I. Qed.',('Check ' if kind=='TYPE' else 'Print ')+n+'.']
    stage.patch.patch_files({work/'assumptions.v':'\n'.join(assumptions)+'\n',work/'contracts.v':'\n'.join(driver)+'\n'})
    a=run(work,['bash','build-jets.sh','--coqc','-q',str(work/'assumptions.v')],'assumptions',1800)
    deps=normal.assumptions((work/'assumptions.log').read_text())
    if set(deps)!=set(results):raise ValueError('incomplete assumption records')
    t=run(work,['bash','build-jets.sh','--coqc','-q',str(work/'contracts.v')],'contracts',900)
    text=(work/'contracts.log').read_text()
    if '...' in text or re.findall(r'(?m)^TAPENV_(TYPE|DEF) (\S+)$',text)!=wanted:raise ValueError('incomplete/truncated records')
    k=run(work,['bash','build-jets.sh','--coqchk','-silent','-o']+['C.'+n for n in meta['roots']],'kernel',5400)
    kernel.kernel((work/'kernel.log').read_text(),sorted((stage.REPO/'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    receipt={'candidate':str(work),'source_commit':meta['source_commit'],'builder_modules':len(entries),
             'results':len(results),'definitions':len(definitions),'closed_results':sum(not d for d in deps.values()),
             'AST':ast,'build':build,'assumptions_check':a,'contract_check':t,'kernel':k,
             'expected_dependencies':{n:sorted(ds) for n,ds in deps.items()},'normal_registration':False,'coverage_added':0,
             'explicit_boundaries':['memcpy_model','readable raw data and address bounds','path length <=128','SHA startup premises','CompCert successful malloc semantics; no malloc-failure theorem','distinct environment unit; no original-unit caller-to-jet transport claim']}
    stage.patch.patch_files({work/'REVIEW.json':json.dumps(receipt,indent=2)+'\n'})
    print(json.dumps({k:v for k,v in receipt.items() if k!='expected_dependencies'},indent=2))


if __name__=='__main__':
    cli=argparse.ArgumentParser();cli.add_argument('--candidate',type=Path,required=True)
    check(cli.parse_args().candidate.resolve())
