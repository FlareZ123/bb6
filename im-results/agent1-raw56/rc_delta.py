#!/usr/bin/env python3
"""Build disjoint Raw56 C1 proof-object deltas on the accepted root closure."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BASE_ID = 15160313745
BASE_RUN = 45912699461
BASE_SHA = '6513147b3929ab6b707225b6592a882025e234d498ed8baca40216489b469b3d'
BASE_NAME = 'raw56-root-frontier-source-accepted'
GROUPS = {
    'special': ('0RD', '1LE', '1RD'),
    '0LF': ('0LF',), '1LF': ('1LF',), '1RF': ('1RF',),
    '0L': ('0LA', '0LB', '0LE'),
    '0R': ('0RA', '0RB', '0RE', '0RF'),
    '1L': ('1LA', '1LB', '1LC'),
    '1R': ('1RA', '1RB', '1RE'),
}
CHOICES = ('0LA','0LB','0LE','0LF','0RA','0RB','0RD','0RE','0RF','1LA','1LB','1LC','1LE','1LF','1RA','1RB','1RD','1RE','1RF')
assert sorted(sum(GROUPS.values(), ())) == sorted(CHOICES)
STANDARD = ('Init', 'Lean', 'Std')


def digest(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def compiler():
    version = subprocess.check_output(['lean', '--version'], text=True).strip()
    assert '4.36.0-rc2,' in version, version
    prefix = Path(subprocess.check_output(['lean', '--print-prefix'], text=True).strip())
    return {'version': version, 'sha256': digest(prefix / 'bin/lean')}


def revision():
    return subprocess.check_output(['git','rev-parse','HEAD'], cwd=ROOT, text=True).strip()


def module_name(name):
    assert re.fullmatch(r'[A-Za-z0-9_]+', name), name
    return name


def imports(path):
    deps = []
    for line in path.read_text().splitlines():
        m = re.match(r'^\s*(?:(?:public|meta)\s+)*import\s+(.+?)\s*$', line)
        if m:
            deps.extend(x for x in m[1].split() if x.split('.')[0] not in STANDARD)
    return deps


def root_for(choice):
    return 'Raw56RC' + ('RD' if choice == '1RD' else choice) + 'All'


def theorem_for(choice):
    return 'BB6.Agent1Raw56.RC' + ('RD' if choice == '1RD' else choice) + '.all_quotient'


def load_base(base):
    base.mkdir(parents=True, exist_ok=False)
    endpoint = f'repos/FlareZ123/bb6/actions/artifacts/{BASE_ID}'
    info = json.loads(subprocess.check_output(['gh','api',endpoint], text=True))
    assert info['name'] == BASE_NAME and info['workflow_run']['id'] == BASE_RUN
    assert not info['expired'] and info['digest'] == 'sha256:' + BASE_SHA
    archive = base.parent / 'raw56-base.zip'
    with archive.open('wb') as f:
        subprocess.run(['gh','api',endpoint+'/zip'], stdout=f, check=True)
    assert digest(archive) == BASE_SHA
    ident = compiler()
    with zipfile.ZipFile(archive) as z:
        manifests = [n for n in z.namelist() if Path(n).name == 'manifest.json']
        assert len(manifests) == 1, manifests
        name = manifests[0]
        data = json.loads(z.read(name))
        assert data['artifact_name'] == BASE_NAME
        assert data['claim']['theorem'] == 'BB6.Agent1Raw56Root.sound19_closed'
        assert data['claim']['weighted_bound'] == 7014
        assert data['lean_version'] == ident['version']
        assert data['lean_binary']['sha256'] == ident['sha256']
        assert data['module_count'] == len(data['modules']) == 747
        prefix = Path(name).parent
        entries = {}
        for e in data['modules']:
            m = module_name(e['module'])
            assert m not in entries and e['olean_path'] == m+'.olean', e
            dst = base / e['olean_path']
            dst.write_bytes(z.read((prefix/e['olean_path']).as_posix()))
            assert digest(dst) == e['olean_sha256'], m
            entries[m] = e
        assert 'Raw56RootConsumer' in entries
        assert all(set(e['project_imports']) <= entries.keys() for e in entries.values())
        (base/'manifest.json').write_text(json.dumps(data)+'\n')
    archive.unlink()
    return entries


def read_delta(folder, available, group, ident, rev):
    data = json.loads((folder/'manifest.json').read_text())
    assert data['base_sha256'] == BASE_SHA and data['compiler'] == ident
    assert data['source_revision'] == rev and data['group'] == group
    expected = GROUPS.get(group, ())
    assert data['choices'] == list(expected), group
    assert data['roots'] == [root_for(c) for c in expected] if expected else data['roots'] == ['Raw56E1RCMixed']
    entries = {}
    for e in data['modules']:
        m = module_name(e['module'])
        assert m not in available and m not in entries, f'object collision: {m}'
        assert digest(folder/(m+'.lean')) == e['source_sha256'], m
        assert digest(folder/(m+'.olean')) == e['olean_sha256'], m
        assert imports(folder/(m+'.lean')) == e['project_imports'], m
        entries[m] = e
    assert set(data['roots']) <= entries.keys(), group
    assert all(set(e['project_imports']) <= available.keys() | entries.keys() for e in entries.values())
    return entries


def build_delta(sources, roots, required, providers, available, out, group, ident, rev, jobs=2):
    out.mkdir(parents=True, exist_ok=False)
    pending = {}
    for p in sources:
        m = module_name(p.stem)
        if m in available:
            assert digest(p) == available[m]['source_sha256'], f'base source mismatch: {m}'
            continue
        assert m not in pending, f'duplicate source: {m}'
        dst = out/(m+'.lean')
        shutil.copy2(p, dst)
        pending[m] = {'module':m, 'source_sha256':digest(dst), 'project_imports':imports(dst)}
    assert set(roots) <= pending.keys(), roots
    for e in pending.values():
        assert set(e['project_imports']) <= available.keys() | pending.keys(), e
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [out,*providers])))
    done = {}
    def compile_one(m):
        result = subprocess.run(['lean','-j','1','-o',m+'.olean',m+'.lean'], cwd=out, env=env,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        log = out/(m+'.log')
        log.write_text(result.stdout)
        if result.returncode or any(x in result.stdout for x in ('sorryAx','native_decide',"declaration uses 'sorry'")):
            print(f'FAILED {m}\n{result.stdout[-16000:]}', flush=True)
            raise RuntimeError(f'Lean failed: {m} ({result.returncode})')
        if m in roots:
            print(f'ROOT {m}\n{result.stdout}', flush=True)
        e = pending[m].copy()
        e['olean_sha256'] = digest(out/(m+'.olean'))
        return m,e
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        while pending:
            ready = sorted(m for m,e in pending.items() if set(e['project_imports']) <= available.keys() | done.keys())
            assert ready, f'cyclic module graph: {list(pending)}'
            for m,e in pool.map(compile_one,ready):
                done[m] = e
            for m in ready: del pending[m]
            print(f'{group}: compiled {len(done)}, pending {len(pending)}', flush=True)
    for m, theorem in required.items():
        subprocess.run([sys.executable,str(HERE.parent/'agent1-raw57/check_axioms.py'),str(out/(m+'.log')),'--require',theorem],check=True)
    manifest = {'base_sha256':BASE_SHA,'compiler':ident,'source_revision':rev,'group':group,
                'choices':list(GROUPS.get(group,())),'roots':roots,'modules':list(done.values()),
                'required_theorems':required}
    (out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')


def generate(group, directory):
    directory.mkdir(parents=True,exist_ok=False)
    def run(script, path, *choices):
        subprocess.run([sys.executable,str(HERE/script),str(path),*choices],cwd=ROOT,check=True)
    if group == 'special':
        run('prepare_rc_rd.py',directory/'rd')
        run('prepare_rc_unary.py',directory/'unary')
    else:
        run('prepare_rc_portfolio.py',directory/'portfolio',*GROUPS[group])
    return sorted(directory.rglob('*.lean'))


def common_sources():
    return [HERE.parent/'agent19-raw40-cut/Raw40Nores.lean',
            HERE.parent/'agent1-ngram/NGramCertificate.lean',
            HERE.parent/'agent47-raw111-cut/SparseNGram.lean',
            HERE.parent/'agent32-raw59/FastBiDFA.lean',
            *(HERE/(x+'.lean') for x in ('UnarySweep','Raw56RDM109','Raw56RDM117','Raw56LEM111','Raw56LEM126',
                                        'Raw56RC_RD_M3','Raw56E1RCCut','Raw56E1RCMixed'))]


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('action',choices=('common','shard','assemble'))
    ap.add_argument('--group',choices=GROUPS)
    ap.add_argument('--base',required=True,type=Path)
    ap.add_argument('--out',required=True,type=Path)
    ap.add_argument('--common',type=Path)
    ap.add_argument('--inputs',type=Path)
    a=ap.parse_args()
    ident,rev=compiler(),revision()
    available=load_base(a.base)
    providers=[a.base]
    if a.action=='common':
        build_delta(common_sources(),['Raw56E1RCMixed'],{'Raw56E1RCMixed':'BB6.Agent1Raw56Root.sound18RC_from_branches'},
                    providers,available,a.out,'common',ident,rev)
        return
    assert a.common is not None
    available.update(read_delta(a.common,available,'common',ident,rev))
    providers.append(a.common)
    if a.action=='shard':
        assert a.group in GROUPS
        roots=[root_for(c) for c in GROUPS[a.group]]
        with tempfile.TemporaryDirectory(prefix='raw56-rc-gen-') as t:
            sources=generate(a.group,Path(t)/'generated')
            build_delta(sources,roots,{root_for(c):theorem_for(c) for c in GROUPS[a.group]},
                        providers,available,a.out,a.group,ident,rev)
        return
    assert a.inputs is not None
    for group in GROUPS:
        folder=a.inputs/('raw56-rc-shard-'+group)
        available.update(read_delta(folder,available,group,ident,rev))
        providers.append(folder)
    build_delta([HERE/'Raw56E1RCAll.lean'],['Raw56E1RCAll'],{'Raw56E1RCAll':'BB6.Agent1Raw56Root.sound18RC_closed'},
                providers,available,a.out,'final',ident,rev,jobs=1)
    data=json.loads((a.out/'manifest.json').read_text())
    data['input_manifests']={p.name:digest(p/'manifest.json') for p in providers}
    (a.out/'manifest.json').write_text(json.dumps(data,indent=2)+'\n')


if __name__=='__main__':main()
