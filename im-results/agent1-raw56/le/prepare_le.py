#!/usr/bin/env python3
"""Replay exact complete E0 children of Raw56 E1=0LE, no abstraction discovery."""
import base64,gzip,hashlib,itertools,json,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
AGENT=HERE.parent
ROOT=HERE.parents[2]
CUT=ROOT/'im-results/agent7-raw49/cut.cpp'
FAR=ROOT/'im-results/agent19-raw40-cut/farbank.cpp'
DISC=AGENT/'discover_abstract_pinned.js'
BIDFA=ROOT/'im-results/agent32-raw59'
SPEC={
'0RB':(8692,2520,'d6d212e9420f894b7dd336cbd0e7c65beb1ac2e2ac501b5be92a6805d8e4714b','17300b1c456d94b3a0961b46372dfc32c0f8da3cedbe2f126df48343be6094cb','b9973ca5c04018fbc91a680a73ff66d615c36827e5924c07701ee72a8b383f25'),
'0RC':(11212,185,'bd5b562758f09fe4e2b4617936cb2e666bcb07e95ae804a24ec2194bd95a843a','a62e73826c9643c8c6f8d5b7d59ababa4d117927a867d93e2866c0da2b8bb71d','5ec9e8318ed60dc43c8fec5070e5c3c90baf687e901d4254505e1bd817974e0d'),
}
def sha(data,expected):assert hashlib.sha256(data).hexdigest()==expected,expected
def blob(path,expected):
    data=path.read_bytes()
    assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==expected,path
def main():
    out=Path(sys.argv[1]).resolve();out.mkdir(parents=True,exist_ok=True)
    selected=sys.argv[2:] or list(SPEC);assert set(selected)<=SPEC.keys()
    raw=gzip.decompress(base64.b64decode((HERE/'inventory-79.json.gz.b64').read_text()))
    sha(raw,'869a651cebab0b5eda351eb783438e7040237b3412747f3ac6265629b840da6f')
    inv=json.loads(raw)
    extra={i:c for c,ids in inv['fmore'] for i in itertools.accumulate(ids)}
    abstract={i:p for p,ids in inv['abs'] for i in itertools.accumulate(ids)}
    for p,h in [(CUT,'88d5dfc4994f8bd203fe3f3def5ea90efda86037'),(FAR,'30cac1862b3b88d7ba596b359a9dc8503163593d'),(DISC,'8fe2ac5d02e9809ea27904da010833e24b331ad9'),(BIDFA/'emit_rungram.py','e11a06c9daf6720ee537e6d2dea27daba20d6723'),(BIDFA/'FastBiDFA.lean','6d31e7e2f081eac524a9c7bb8bd33e55bc1dfd7f'),(AGENT/'emit_rc_rd.py','f6753bf0e6368a66eadb148d5df61d491068e54a')]:blob(p,h)
    for name,src in [('cut',CUT),('farbank',FAR)]:subprocess.run(['g++','-O3','-std=c++20',str(src),'-o',str(out/name)],check=True)
    sys.path.insert(0,str(BIDFA));from emit_rungram import emit
    for v in selected:
        offset,count,ht,ho,hf=SPEC[v];stop=offset+count
        assert not any(offset<=i<stop for i in inv['remaining'])
        assert not any(offset<=row[0]<stop for row in inv['late'])
        assert not any(offset<=row[0]<stop for row in inv['sat'])
        stem=out/v;parent=f'1RB---_1RC---_0RD---_1LD1LE_{v}0LE_------'
        subprocess.run([str(out/'cut'),parent,'1000','32','6',str(stem)],check=True)
        tree,opens,f5,bank=[stem.with_suffix(s) for s in ('.json','.open','.far','.bank')]
        sha(tree.read_bytes(),ht);sha(opens.read_bytes(),ho)
        rows=opens.read_text().splitlines();assert len(rows)==len(set(rows))==count
        inp=''.join(f"{i} {t.replace('_','')}\n" for i,t in enumerate(rows)).encode()
        with f5.open('wb') as f:subprocess.run([str(out/'farbank'),'5'],input=inp,stdout=f,check=True)
        sha(f5.read_bytes(),hf)
        bank.write_bytes(f5.read_bytes()+''.join(f'{i-offset} {c}\n' for i,c in sorted(extra.items()) if offset<=i<stop).encode())
        got={int(x.split()[0]) for x in bank.read_text().splitlines()};assert len(got)==len(bank.read_text().splitlines())
        qs=[dict(id=i-offset,table=rows[i-offset],p=p) for i,p in sorted(abstract.items()) if offset<=i<stop]
        records=json.loads(subprocess.check_output(['node',str(HERE/'le_replay.cjs'),str(DISC)],input=json.dumps(qs).encode()))
        gen=out/(v+'gen');gen.mkdir(exist_ok=True);proven={};mods=[]
        for rec in records:
            i=rec['id'];assert rec['table']==rows[i] and i not in got
            mod=f'Raw56LE{v}BiDFA{i}';ns=f'BB6.Agent1Raw56.LE{v}BiDFA{i}'
            text='\n'.join(['import FastBiDFA','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace '+ns,'open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram BB6.Agent32FastBiDFA',emit(i,rec['table'],*rec['dfa'],[rec['states'],rec['edges']]),'end '+ns,''])
            (gen/(mod+'.lean')).write_text(text);mods.append(mod);proven[i]=ns+f'.M{i}'
        assert got|set(proven)==set(range(count)) and len(got)+len(proven)==count
        mod='Raw56LE'+v;ns='BB6.Agent1Raw56.LE'+v;s=(AGENT/'emit_rc_rd.py').read_text()
        patches={"NS = 'BB6.Agent1Raw56.RCRD'":f'NS = {ns!r}',"MOD = 'Raw56RCRD'":f'MOD = {mod!r}',"PARENT = '1RB---_1RC---_0RD1RD_1LD1LE_---0RC_------'":f'PARENT = {parent!r}',"assert len(rows)==len(set(rows))==102 and rows[3]==M3":f'assert len(rows)==len(set(rows))=={count}',"assert set(bank)==set(range(102))-{3}":f'assert set(bank)==set(range({count}))-set({proven!r})',"['Raw40Nores','Raw56RC_RD_M3']":repr(['Raw40Nores',*mods]),"return f'.proven {PROOF}.table {PROOF}.never' if i==3 else far(bank[i],p)":f'proven = {proven!r}\n            return f\'.proven {{proven[i]}}.table {{proven[i]}}.never\' if i in proven else far(bank[i],p)'}
        for a,b in patches.items():assert s.count(a)==1,a;s=s.replace(a,b)
        emitter=out/('emit_'+v+'.py');emitter.write_text(s)
        subprocess.run([sys.executable,str(emitter),str(tree),str(opens),str(bank),str(gen)],check=True)
        manifest=gen/'manifest.json';manifest.write_text(json.dumps([[x,['FastBiDFA']] for x in mods]+json.loads(manifest.read_text()),indent=2)+'\n')
        print(v,'FAR',len(got),'BiDFA',len(proven),flush=True)
if __name__=='__main__':main()
