"""Deterministic run/block-run abstract-stack closure and exact FAR replay."""
from collections import defaultdict, deque
from pathlib import Path
import argparse, hashlib, json, subprocess, sys, tempfile

HERE=Path(__file__).resolve().parent
IM=HERE.parent
sys.path.insert(0,str(IM/'agent2-tnf-raw124'))
import replay_fast_cut as cut
from sibling_witnesses import from_runs, emit
from bidfa_emit import witness

def stack_dfa(kind, params):
    # Read a finite stack from its far end, append bits at the near end.
    # The blank state absorbs zero pushes. Nonblank stacks retain a bounded
    # list of runs of block symbols and a partially filled terminal block.
    k=params[0]
    if kind=='run':
        _,tz,to,pz,po=params; width=1; align=0
    else:
        _,width,t,m,align=params;tz=to=t;pz=po=m
    states=[((),0,0)];idx={states[0]:0};tr=[[-1,-1]]
    def push(i,b):
        if tr[i][b]>=0:return tr[i][b]
        runs,phase,partial=states[i]
        if i==0 and b==0:st=states[0]
        else:
            if i==0:phase=align
            partial=2*partial+b;phase+=1
            if phase==width:
                if runs and runs[0][0]==partial:
                    n=runs[0][1];t,m=(to,po) if partial and kind=='run' else (tz,pz)
                    runs=((partial,n+1 if n<t+m-1 else t),)+runs[1:]
                else:runs=((partial,1),)+runs[:k-1]
                phase=partial=0
            st=(runs,phase,partial)
        if st not in idx:idx[st]=len(states);states.append(st);tr.append([-1,-1])
        tr[i][b]=idx[st]
        return tr[i][b]
    return push,tr

def discover(table,kind,params,cap=150000):
    p=[table[i:i+3] for i in range(0,36,3)]
    push,tr=zip(*(stack_dfa(kind,params) for _ in range(2)))
    edges=[defaultdict(set),defaultdict(set)];wait=[defaultdict(list),defaultdict(list)]
    seen={(0,0,0,0)};todo=deque(seen)
    for e in edges:e[0].add((0,0))
    def add(q,a,l,r):
        s=q,a,l,r
        if s not in seen:
            if len(seen)>=cap or p[2*q+a]=='---':raise ValueError(f'failed closure {table}')
            seen.add(s);todo.append(s)
    def pop(s,b,x):
        q,a,l,r=s;w,d,n=p[2*q+a];w=int(w);n=ord(n)-65
        if d=='R':add(n,b,push[0](l,w),x)
        else:add(n,b,x,push[1](r,w))
    while todo:
        s=todo.popleft();q,a,l,r=s;w,d,n=p[2*q+a];w=int(w);side=int(d=='R');old=l if side else r;dest=push[1-side](old,w);e=w,old
        if e not in edges[1-side][dest]:
            edges[1-side][dest].add(e)
            for st in wait[1-side][dest]:pop(st,*e)
        x=r if side else l;wait[side][x].append(s)
        for b,y in sorted(edges[side][x]):pop(s,b,y)
    return [[max(0,x) for row in a for x in row] for a in tr],len(seen)

def emit_witnesses(spec,opens,stem,out,tmp):
    ref={}
    for key,(kind,*params) in spec['params'].items():
        i=int(key);d,n=discover(opens[i],kind,params)
        assert len(witness(opens[i],*d)[1])==n
        d=from_runs(opens[i],d)
        name=stem+'Wide'+str(i);ns='BB6.Agent2'+name
        with tempfile.TemporaryDirectory() as folder:
            folder=Path(folder);n2,e=emit(i,opens[i],*d,folder)
            assert n2<=n
            for f in folder.glob('*.lean'):
                target=out/f.name.replace('Raw118Wide'+str(i),name)
                target.write_text(f.read_text().replace('Raw118Wide'+str(i),name).replace('BB6Coverage.Agent1BiDFAWide.M'+str(i),ns))
        ref[i]=(name,ns)
        print('INDEXED',i,kind,n,n2,e,flush=True)
    return ref

def main(out,branch='0LE'):
    out.mkdir(parents=True,exist_ok=True)
    suffix='' if branch=='0LE' else '-'+branch
    spec=json.loads((HERE/('parameters'+suffix+'.json')).read_text())
    bankfile=HERE/('far-bank'+suffix+'.txt')
    bound=spec.get('bound',3006)
    assert spec['branch']==branch
    with tempfile.TemporaryDirectory() as folder:
        tmp=Path(folder);part=tmp/'partition';prefix=tmp/'tree';bank=tmp/'bank'
        subprocess.run(['g++','-std=c++20','-O3',str(IM/'agent2-tnf-raw124'/'fast_partition.cpp'),'-o',str(part)],check=True)
        subprocess.run([str(part),cut.PARENT+branch,str(spec['cap']),str(spec['lookback']),str(prefix)],check=True)
        opens=prefix.with_suffix('.open').read_bytes();tree=prefix.with_suffix('.json').read_bytes()
        assert hashlib.sha256(opens).hexdigest()==spec['open_sha256']
        assert hashlib.sha256(tree).hexdigest()==spec['tree_sha256']
        subprocess.run(['g++','-std=c++17','-O3',str(IM/'agent7-raw123'/'bank.cpp'),'-o',str(bank)],check=True)
        hits=subprocess.run([str(bank),str(bankfile)],input=opens.decode(),capture_output=True,text=True,check=True).stdout
        rows=[s.split() for s in hits.splitlines()]
        codes=bankfile.read_text().split()
        assert len(rows)==spec.get('open_count',5961) and all(int(i)==j for j,(i,_) in enumerate(rows))
        remaining={int(i) for i,c in rows if c=='-'}
        assert remaining==set(map(int,spec['params'])) | set(map(int,spec.get('late_queries',{})))
        assert len(codes)==spec.get('bank_count',193)
        spec.update(bank=codes,far=[codes.index(c) if c!='-' else -1 for i,c in rows],remaining=[])
    cut.emit_sibling_witnesses=emit_witnesses
    cut.replay(spec,out)
    assert not (out/f'Raw124New{branch}.remaining').read_text().strip()
    (out/f'Raw124New{branch}Complete.lean').write_text(f"""import Raw124New{branch}Cut
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent2Raw124New{branch}
open BB6Coverage BB6.Agent13BlankDelay

theorem bound_all : ∀ m, compatible branch m → WeightedBound {bound} m := by
  intro m hm
  rcases branch_sound m hm with hb | ⟨e,he,_⟩
  · exact hb
  · have hnil : residuals = [] := List.length_eq_zero_iff.mp residual_count
    rw [hnil] at he
    simp at he

#print axioms bound_all
end BB6.Agent2Raw124New{branch}
""")

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,required=True);parser.add_argument('--branch',choices=['0LE','1LA'],default='0LE');a=parser.parse_args();main(a.out,a.branch)
