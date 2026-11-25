"""Wide-window discovery, context quotient, independent replay and Lean source emission."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent16-raw118"))
from bidfa_emit import witness, boolstr

def ngram_dfa(v,k):
    ed=[(int(x.split(':')[0]),e) for x in v.rstrip(',').split(',')
        for e in range(2) if int(x.split(':')[1])&(1<<e)]
    nodes={0}|{x for x,e in ed}|{(x>>1)|(e<<(k-1)) for x,e in ed}
    ids={x:i for i,x in enumerate(sorted(nodes))}
    tr=[-1]*(2*len(nodes))
    for x,e in ed:
        src=(x>>1)|(e<<(k-1))
        tr[2*ids[src]+(x&1)]=ids[x]
    return tr,ids

def initial_data(text):
    a=text.split()
    k=int(a[1]); M=1<<k
    l,il=ngram_dfa(a[3],k);r,ir=ngram_dfa(a[4],k)
    states=[(x//M//M,il[(x//M)%M],ir[x%M]) for x in map(int,a[5].rstrip(',').split(','))]
    assert len(states)==int(a[2])
    return [l,r],states

def quotient_context(d,states,side):
    n=len(d[side])//2
    contexts=[set() for _ in range(n)]
    for s,l,r in states:
        contexts[l if side==0 else r].add((s,r if side==0 else l))
    def classify(sig):
        ix={}
        return [ix.setdefault(x,len(ix)) for x in sig]
    p=classify([tuple(sorted(c)) for c in contexts])
    while True:
        q=classify([(p[i],*(p[x] if x>=0 else -1 for x in d[side][2*i:2*i+2])) for i in range(n)])
        if q==p:break
        p=q
    new=[-1]*(2*(max(p)+1))
    for i in range(n):
        for b in range(2):
            x=d[side][2*i+b]
            if x>=0:
                assert new[2*p[i]+b] in [-1,p[x]]
                new[2*p[i]+b]=p[x]
    d[side]=new
    states=list({(s,p[l],r) if side==0 else (s,l,p[r]) for s,l,r in states})
    return states,n-len(new)//2

def compress(text):
    d,states=initial_data(text)
    original=(len(states),len(d[0])//2,len(d[1])//2)
    while True:
        states,x=quotient_context(d,states,0)
        states,y=quotient_context(d,states,1)
        if not x+y:break
    return [[max(0,x) for x in a] for a in d],original,len(states)

def emit(i,table,dl,dr,outdir):
    es,states=witness(table,dl,dr)
    assert len(dl)//2<65536 and len(dr)//2<65536
    ns=f"BB6Coverage.Agent1BiDFAWide.M{i}"
    base=f"Raw118Wide{i}"
    outdir.mkdir(parents=True,exist_ok=True)
    common=["set_option maxRecDepth 100000","set_option maxHeartbeats 0",
            f"namespace {ns}",
            "open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck"]
    def write(mod,imports,body):
        (outdir/(mod+".lean")).write_text("\n".join([
            *(f"import {x}" for x in imports),*common,*body,f"end {ns}",""]))
    data=['def table : PartialMachine := fun s =>','  match s.1.val,s.2 with']
    p=table.replace('_','')
    for j in range(12):
        m=p[3*j:3*j+3]
        if m!='---':data.append(f'  | {j//2},{boolstr(j%2)} => some (some ⟨{boolstr(m[0]=="1")},{boolstr(m[1]=="R")},{ord(m[2])-65}⟩)')
    data.append('  | _,_ => none')
    def node(mid):
        q,a,x,y=states[mid]
        return f'⟨{q},{boolstr(a)},{x},{y}⟩'
    def tree(lo,hi):
        if lo==hi:return '.empty'
        mid=(lo+hi)//2
        return f'(.node {tree(lo,mid)} {node(mid)} {tree(mid+1,hi)})'
    def make(lo,hi):
        if lo==hi:return '.empty'
        name=f't{lo}_{hi}'
        if hi-lo<=16:data.append(f'def {name} : Tree := {tree(lo,hi)}')
        else:
            mid=(lo+hi)//2;l,r=make(lo,mid),make(mid+1,hi)
            data.append(f'def {name} : Tree := .node {l} {node(mid)} {r}')
        return name
    root=make(0,len(states))
    data.append('def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#'+str(dl)+',#'+str(dr)+',')
    for side,e in enumerate(es):
        rows=[[] for _ in range(len([dl,dr][side])//2)]
        for dest,b,src in e:rows[dest].append(f'({boolstr(b)},{src})')
        data.append('  #['+','.join('['+','.join(row)+']' for row in rows)+'],')
    data.append(f'  {root}⟩')
    write(base+"Data",["IndexedBiDFA"],data)
    step="BB6Coverage.Agent1IndexedBiDFA.stepOK table cert"
    def join(lo,hi,body,l,r):
        mid=(lo+hi)//2;name=f't{lo}_{hi}';thm=f'check{lo}_{hi}'
        body.append(f'theorem node{mid} : {step} {node(mid)} = true := by decide')
        body.append(f'theorem {thm} : {name}.all ({step}) = true := Tree.all_node node{mid} {l} {r}')
        return thm
    def blocks(lo,hi,body):
        if lo==hi:return '(by rfl)'
        name=f't{lo}_{hi}';thm=f'check{lo}_{hi}'
        if hi-lo<=16:
            body.append(f'theorem {thm} : {name}.all ({step}) = true := by decide')
            return thm
        mid=(lo+hi)//2;l,r=blocks(lo,mid,body),blocks(mid+1,hi,body)
        return join(lo,hi,body,l,r)
    chunks=[];top=[]
    def split(lo,hi):
        if lo==hi:return '(by rfl)'
        if hi-lo<=512:
            mod=base+f"Chunk{len(chunks):03}"
            body=[];thm=blocks(lo,hi,body)
            write(mod,[base+"Data"],body)
            chunks.append(mod)
            return thm
        mid=(lo+hi)//2;l,r=split(lo,mid),split(mid+1,hi)
        return join(lo,hi,top,l,r)
    checked=split(0,len(states))
    top += [f'theorem checked : cert.states.all ({step}) = true := {checked}',
            'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm',
            '#print axioms never']
    write(base,[base+"Data",*chunks],top)
    return len(states),sum(map(len,es))

def main(i):
    roster=(ROOT/"raw118-hard87.tsv").read_bytes()
    assert hashlib.sha256(roster).hexdigest()=="0fd10d3adcc48fba9badb4357ad3b19453f5215ce35fdb57f38034ebc3933c0c"
    tables={int(i):t for i,t in (x.split() for x in roster.decode().splitlines())}
    assert len(tables)==87 and all(t.count("---")==1 for t in tables.values())
    widths=json.loads((ROOT/"raw118-wide-widths.json").read_text())
    k,n=widths[str(i)];table=tables[i]
    with tempfile.TemporaryDirectory() as temp:
        exe=Path(temp)/"ngram"
        subprocess.run(["g++","-O3","-std=c++17",str(ROOT/"ngram_wide.cpp"),"-o",str(exe)],check=True)
        result=subprocess.check_output([str(exe),str(k)],input=f"{i} {table}\n",text=True)
    assert tuple(map(int,result.split()[:3]))==(i,k,n)
    d,original,projected=compress(result)
    out=ROOT/"wide-generated"
    states,edges=emit(i,table,*d,out)
    assert states<=projected
    record={"index":i,"table":table,"width":k,"original":original,"projected":projected,
            "left":d[0],"right":d[1],"states":states,"edges":edges}
    (out/f"Raw118Wide{i}.json").write_text(json.dumps(record,indent=2)+"\n")
    print(f"WIDE {i} width={k} original={original} quotient={len(d[0])//2}x{len(d[1])//2} states={states} edges={edges}")

if __name__=="__main__":
    main(int(sys.argv[1]))
