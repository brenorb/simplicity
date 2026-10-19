"""Isolate checked ordinary square dependencies for separate-buffer callers."""
import importlib.util
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sp = importlib.util.spec_from_file_location('separate_square_checked_basis', HERE.parent / 'secp-square-integration/verify.py')
p = importlib.util.module_from_spec(sp)
sp.loader.exec_module(p)
s = p.s
SOURCE_REV = '66de0fed4094065d9c79e90dcc641b8306d21656'


def prepare():
    if (HERE / 'PREPARATION.json').exists():
        raise ValueError('separate square preparation already exists')
    p.check()
    parent, prep, built = p.built()
    before, index = s.input_map(), s.index_hash()
    work = Path(tempfile.mkdtemp(prefix='jet-square-separate-basis-', dir='/private/tmp'))
    ext = Path(tempfile.mkdtemp(prefix='jet-square-separate-', dir='/private/tmp'))
    raw = subprocess.check_output(['git', 'archive', SOURCE_REV, 'Coq', 'C', 'Haskell'], cwd=REPO)
    with tarfile.open(fileobj=io.BytesIO(raw)) as archive:
        archive.extractall(work, filter='data')
    if any((work / 'Coq').rglob('*.vo')):
        raise ValueError('source archive unexpectedly contains local objects')
    payloads = p.a.payloads()
    s.changed({work / n: row['raw'].decode() for n, row in payloads.items()})
    sources, objects = {}, {}
    for n, row in prep['sources'].items():
        source, obj = work / n, (parent / n).with_suffix('.vo')
        if s.sha(source.read_bytes()) != row['sha256'] or s.sha(obj.read_bytes()) != built['source_objects'][n]:
            raise ValueError('checked square source/object pair differs: ' + n)
        shutil.copyfile(obj, source.with_suffix('.vo'))
        sources[n], objects[n] = row['sha256'], built['source_objects'][n]
    if before != s.input_map() or index != s.index_hash():
        raise ValueError('main source/staging changed during separate square preparation')
    r = dict(candidate=str(work), extension=str(ext), source_revision=SOURCE_REV,
        sources=sources, source_objects=objects, main_inputs=before, staged_patch_sha256=index,
        parent_checked_sha256=s.sha((p.HERE / 'CHECKED.json').read_bytes()),
        preparer_sha256=s.sha(Path(__file__).read_bytes()), normal_registration=False, coverage_added=0)
    s.changed({HERE / 'PREPARATION.json': json.dumps(r, indent=2) + '\n'})
    print('Prepared ' + str(work) + ' and ' + str(ext) + ': ' + str(len(sources)) + ' exact checked square source/object pairs', flush=True)


def identity():
    r = json.loads((HERE / 'PREPARATION.json').read_text())
    work, ext = Path(r['candidate']), Path(r['extension'])
    if (work == REPO or REPO in work.parents or work.is_symlink() or ext.is_symlink() or ext == work or
            r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
            r['parent_checked_sha256'] != s.sha((p.HERE / 'CHECKED.json').read_bytes()) or
            r['preparer_sha256'] != s.sha(Path(__file__).read_bytes())):
        raise ValueError('separate square preparation identity differs')
    for n, digest in r['sources'].items():
        if s.sha((work / n).read_bytes()) != digest or s.sha((work / n).with_suffix('.vo').read_bytes()) != r['source_objects'][n]:
            raise ValueError('separate square inherited source/object differs: ' + n)
    return work, ext, r


if __name__ == '__main__':
    if len(sys.argv) != 2 or sys.argv[1] not in {'prepare', 'check'}:
        raise SystemExit('usage: prepare.py prepare|check')
    if sys.argv[1] == 'prepare':
        prepare()
    else:
        print(identity()[0])
