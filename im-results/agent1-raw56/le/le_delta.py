#!/usr/bin/env python3
"""Link accepted Raw56 root and RC common objects, compile independent LE child cuts."""
import argparse,hashlib,json,os,subprocess,sys,tempfile,zipfile
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
import rc_delta as rc
COMMON_ID=15222016893
COMMON_RUN=46045652695
COMMON_SHA='e4ac362aa71659198c9ab947578e036d06abe02ae1a8603b6a42a1147644a572'
COMMON_REV='7d86a938027448a2c54a2088eb337aae97afb9b9'
CHOICES=('0RB','0RC')
def load_common(folder):
    endpoint=f'repos/FlareZ123/bb6/actions/artifacts/{COMMON_ID}'
    info=json.loads(subprocess.check_output(['gh','api',endpoint],text=True))
    assert info['name']=='raw56-rc-common' and info['workflow_run']['id']==COMMON_RUN
    assert not info['expired'] and info['digest']=='sha256:'+COMMON_SHA
    archive=folder.parent/'raw56-common.zip'
    with archive.open('wb') as f:subprocess.run(['gh','api',endpoint+'/zip'],stdout=f,check=True)
    assert rc.digest(archive)==COMMON_SHA
    folder.mkdir(parents=True,exist_ok=False)
    with zipfile.ZipFile(archive) as z:
        manifest=[n for n in z.namelist() if Path(n).name=='manifest.json'];assert len(manifest)==1
        prefix=Path(manifest[0]).parent
        data=json.loads(z.read(manifest[0]))
        (folder/'manifest.json').write_bytes(z.read(manifest[0]))
        for e in data['modules']:
            m=rc.module_name(e['module'])
            for suf in ('.lean','.olean'):
                name=m+suf
                (folder/name).write_bytes(z.read((prefix/name).as_posix()))
    archive.unlink()
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('action',choices=('shard','assemble'))
    ap.add_argument('--choice',choices=CHOICES)
    ap.add_argument('--base',required=True,type=Path)
    ap.add_argument('--common',required=True,type=Path)
    ap.add_argument('--out',required=True,type=Path)
    ap.add_argument('--inputs',type=Path)
    a=ap.parse_args();ident=rc.compiler();rev=rc.revision()
    available=rc.load_base(a.base);load_common(a.common)
    available.update(rc.read_delta(a.common,available,'common',ident,COMMON_REV))
    providers=[a.base,a.common]
    for v in CHOICES:rc.GROUPS['le-'+v]=(v,)
    rc.root_for=lambda v:'Raw56LE'+v+'All'
    rc.theorem_for=lambda v:'BB6.Agent1Raw56.LE'+v+'.all_quotient'
    if a.action=='shard':
        assert a.choice
        v=a.choice;root=rc.root_for(v)
        with tempfile.TemporaryDirectory(prefix='raw56-le-gen-') as t:
            gen=Path(t)/'generated'
            subprocess.run([sys.executable,str(HERE/'prepare_le.py'),str(gen),v],check=True)
            rc.build_delta(sorted(gen.rglob('*.lean')),[root],{root:rc.theorem_for(v)},providers,available,a.out,'le-'+v,ident,rev)
        return
    assert a.inputs is not None
    for v in CHOICES:
        folder=a.inputs/('raw56-le-shard-'+v)
        available.update(rc.read_delta(folder,available,'le-'+v,ident,rev));providers.append(folder)
    roots=['Raw56E1LECut','Raw56E1LETwoClosed']
    rc.build_delta([HERE/(m+'.lean') for m in roots],roots,{roots[0]:'BB6.Agent1Raw56E1LE.sound14',roots[1]:'BB6.Agent1Raw56E1LE.sound12_closed'},providers,available,a.out,'le-two-final',ident,rev,jobs=1)
    data=json.loads((a.out/'manifest.json').read_text())
    data['input_manifests']={p.name:rc.digest(p/'manifest.json') for p in providers}
    data['common_sha256']=COMMON_SHA
    (a.out/'manifest.json').write_text(json.dumps(data,indent=2)+'\n')
if __name__=='__main__':main()
