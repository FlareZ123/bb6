"""Regenerate and independently check indexed stack-summary certificates."""
from pathlib import Path
import subprocess, sys, json
from collections import defaultdict

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'agent1-bidfa-sat'))
from wide_cert import ngram_dfa,quotient_context,emit
from bidfa_emit import witness

def quotient(d, states):
    while True:
        states,x=quotient_context(d,states,0)
        states,y=quotient_context(d,states,1)
        if not x+y:break
    return [[max(0,x) for x in a] for a in d]

def from_windows(lines):
    k,m,n=map(int,lines[0].split());M=1<<k;N=1<<m
    l,il=ngram_dfa(lines[1],k);r,ir=ngram_dfa(lines[2],m)
    states=[(x//N//M,il[(x//N)%M],ir[x%N]) for x in map(int,lines[3].rstrip(',').split(','))]
    assert len(states)==n
    return quotient([l,r],states)

def from_runs(table,d):
    es,states=witness(table,*d)
    incomplete=[[-1]*len(a) for a in d]
    for side in range(2):
        for dest,b,src in es[side]:incomplete[side][2*src+int(b)]=dest
    return quotient(incomplete,[(int(q)*2+int(a),l,r) for q,a,l,r in states])

def emit_sibling_witnesses(spec,opens,stem,out,tmp):
    """The Python witness replay, not the discovery search, drives the Lean checker."""
    groups=defaultdict(list)
    for key,p in spec['params'].items():groups[tuple(p[:-1] if p[0]=='w' else p)].append(int(key))
    for kind in ('sparse_ngram','run_ngram'):
        subprocess.run(['g++','-std=c++20','-O3',str(ROOT/(kind+'.cpp')),'-o',str(tmp/kind)],check=True)
    ref={}
    for p,ids in groups.items():
        tables=''.join(f'{i} {opens[i]}\n' for i in ids)
        if p[0]=='w':
            k,m,cap=p[1:];args=[k,m,cap];exe=tmp/'sparse_ngram'
        else:
            k,tz,to,pz,po,cap=p[1:];args=[k,tz,to,pz,po]*2+[cap];exe=tmp/'run_ngram'
        res=subprocess.run([str(exe),*map(str,args)],input=tables,text=True,capture_output=True,check=True)
        lines=res.stdout.splitlines();pairs={}
        if p[0]=='w':
            assert len(lines)%5==0
            for j in range(0,len(lines),5):
                i=int(lines[j]);assert int(lines[j+1].split()[2])==spec['params'][str(i)][-1]
                pairs[i]=from_windows(lines[j+1:j+5])
        else:
            for line in lines:
                i,d=line.split(' ',1);i=int(i);pairs[i]=from_runs(opens[i],json.loads(d))
        assert set(pairs)==set(ids),(p,ids,list(pairs),res.stderr)
        for i,d in pairs.items():
            name=stem+'Wide'+str(i);ns='BB6.Agent2'+name
            with __import__('tempfile').TemporaryDirectory() as folder:
                folder=Path(folder)
                n,e=emit(i,opens[i],*d,folder)
                for f in folder.glob('*.lean'):
                    target=out/f.name.replace('Raw118Wide'+str(i),name)
                    target.write_text(f.read_text().replace('Raw118Wide'+str(i),name).replace('BB6Coverage.Agent1BiDFAWide.M'+str(i),ns))
            ref[i]=(name,ns)
            print('INDEXED',i,n,e,flush=True)
    assert set(ref)==set(map(int,spec['params']))
    return ref
