#!/usr/bin/env python3
"""Regenerate pinned candidate proofs for the 16 other E1=0RC children.
The untrusted search inputs are checked by original Lean canonicalCheck/FastBiDFA.
"""
import json,subprocess,sys,hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
CUT=ROOT/'im-results/agent7-raw49/cut.cpp'
FAR=ROOT/'im-results/agent19-raw40-cut/farbank.cpp'
# Exact historical Agent25 abstraction blob; shared discovery continues evolving.
DISC=HERE/'discover_abstract_pinned.js'
BIDFA=ROOT/'im-results/agent32-raw59'

def blob(path, expected):
    data=path.read_bytes()
    assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==expected,path

def sha(path, expected):assert hashlib.sha256(path.read_bytes()).hexdigest()==expected,path

def params(s):
    typ=s[0]; a=list(map(int,s[1:].split(',')))
    if typ=='n':return a[0]
    if typ=='r':return a
    if typ=='l':return dict(zip(('lag','r','c0','c1','m0','m1'),a))
    assert typ=='b';return dict(k=a[0],c=a[1],m=a[2],periods=a[3:])

def main():
    out=Path(sys.argv[1]).resolve();out.mkdir(exist_ok=True,parents=True)
    selected=set(sys.argv[2:]);spec=[l.split('|') for l in (HERE/'rc_portfolio.tsv').read_text().splitlines() if l and not l.startswith('#')]
    assert not selected-{r[0] for r in spec}
    for p,d in [(CUT,'88d5dfc4994f8bd203fe3f3def5ea90efda86037'),(FAR,'30cac1862b3b88d7ba596b359a9dc8503163593d'),(DISC,'8fe2ac5d02e9809ea27904da010833e24b331ad9'),(BIDFA/'emit_rungram.py','e11a06c9daf6720ee537e6d2dea27daba20d6723'),(BIDFA/'FastBiDFA.lean','6d31e7e2f081eac524a9c7bb8bd33e55bc1dfd7f'),(HERE/'emit_rc_rd.py','f6753bf0e6368a66eadb148d5df61d491068e54a')]:blob(p,d)
    for name,src in [('cut',CUT),('farbank',FAR)]:subprocess.run(['g++','-O3','-std=c++20',str(src),'-o',str(out/name)],check=True)
    sys.path.insert(0,str(BIDFA));from emit_rungram import emit
    for v,n,h1,h2,h3,f6,lates,certs in spec:
        if selected and v not in selected:continue
        count=int(n);stem=out/v;parent=f'1RB---_1RC---_0RD{v}_1LD1LE_---0RC_------'
        subprocess.run([str(out/'cut'),parent,'1000','32','6',str(stem)],check=True)
        tree,opens,f5,bank=[stem.with_suffix(s) for s in ('.json','.open','.far','.bank')]
        rows=opens.read_text().splitlines();assert len(rows)==len(set(rows))==count
        inp=''.join(f"{i} {t.replace('_','')}\n" for i,t in enumerate(rows)).encode()
        with f5.open('wb') as f:subprocess.run([str(out/'farbank'),'5'],input=inp,stdout=f,check=True)
        for p,h in ((tree,h1),(opens,h2),(f5,h3)):sha(p,h)
        bank.write_bytes(f5.read_bytes()+''.join(s.replace(':',' ')+'\n' for s in f6.split(';') if s).encode())
        got={int(x.split()[0]) for x in bank.read_text().splitlines()};assert len(got)==len(bank.read_text().splitlines())
        late={}
        for x in lates.split(';'):
            if not x:continue
            i,t=x.split(':');a=t.split(',');late[int(i)]=[a[0],*map(int,a[1:])]
        qs=[]
        for x in certs.split(';'):
            if not x:continue
            i,p,s,e=x.split(':');i=int(i);qs.append(dict(id=i,table=rows[i],params=params(p),states=int(s),edges=int(e)))
        records=json.loads(subprocess.check_output(['node',str(HERE/'portfolio.cjs'),str(DISC)],input=json.dumps(qs).encode()))
        proven={};mods=[];gen=out/(v+'gen');gen.mkdir(exist_ok=True)
        for rec in records:
            i=rec['id'];assert rec['table']==rows[i] and i not in got
            mod=f'Raw56RC{v}BiDFA{i}';ns=f'BB6.Agent1Raw56.RC{v}BiDFA{i}'
            text='\n'.join(['import FastBiDFA','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace '+ns,'open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram BB6.Agent32FastBiDFA',emit(i,rec['table'],*rec['dfa'],[rec['states'],rec['edges']]),'end '+ns,''])
            (gen/(mod+'.lean')).write_text(text);mods.append(mod);proven[i]=ns+f'.M{i}'
        assert got|set(proven)|set(late)==set(range(count)) and len(got)+len(proven)+len(late)==count
        mod='Raw56RC'+v;ns='BB6.Agent1Raw56.RC'+v;s=(HERE/'emit_rc_rd.py').read_text()
        patches={"NS = 'BB6.Agent1Raw56.RCRD'":f'NS = {ns!r}',"MOD = 'Raw56RCRD'":f'MOD = {mod!r}',"PARENT = '1RB---_1RC---_0RD1RD_1LD1LE_---0RC_------'":f'PARENT = {parent!r}',"assert len(rows)==len(set(rows))==102 and rows[3]==M3":f'assert len(rows)==len(set(rows))=={count}',"assert set(bank)==set(range(102))-{3}":f'assert set(bank)==set(range({count}))-set({proven!r})-set({late!r})',"['Raw40Nores','Raw56RC_RD_M3']":repr(['Raw40Nores',*mods]),"return f'.proven {PROOF}.table {PROOF}.never' if i==3 else far(bank[i],p)":f'proven = {proven!r}\n            late = {late!r}\n            if i in late:return ordinary(late[i],p)\n            return f\'.proven {{proven[i]}}.table {{proven[i]}}.never\' if i in proven else far(bank[i],p)'}
        if v=='0LF':patches['BOUND = 7014']='BOUND = 10000'
        for a,b in patches.items():assert s.count(a)==1,a;s=s.replace(a,b)
        emitter=out/('emit_'+v+'.py');emitter.write_text(s)
        subprocess.run([sys.executable,str(emitter),str(tree),str(opens),str(bank),str(gen)],check=True)
        manifest=gen/'manifest.json';manifest.write_text(json.dumps([[x,['FastBiDFA']] for x in mods]+json.loads(manifest.read_text()),indent=2)+'\n')
        print(v,'FAR',len(got),'BiDFA',len(proven),'late',len(late),flush=True)
if __name__=='__main__':main()
