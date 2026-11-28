import json
from pathlib import Path
from verify import build,saturate

def quotient(E,A,U):
    P=U+1
    rows=[]
    for s in E:
        r=[]
        while s:
            k=s&-s;s-=k;r.append(k.bit_length()-1)
        rows.append(r)
    p=[int(i==U) for i in range(P)]
    while True:
        d={};q=[d.setdefault((p[i],tuple(tuple(sorted({p[t] for t in rows[i*A+x]})) for x in range(A))),len(d)) for i in range(P)]
        if len(set(p))==len(d):p=q;break
        p=q
    edges=[[None]*A for _ in set(p)]
    for i in range(P):
        for x in range(A):edges[p[i]][x]=sorted({p[t] for t in rows[i*A+x]})
    return p,edges,p[U]

def emit(g,path):
    rules,bad,U,A=build(g,13);safe,E,rounds=saturate(rules,bad,U,A);assert safe
    p,edges,final=quotient(E,A,U);n=len(g['head']);prev=[[] for _ in range(n)];prev[0]=[0]
    for i,row in enumerate(g['delta']):
        for a,j in row:prev[j].append(i)
    def arr(xs):return '#['+','.join(xs)+']'
    def lst(xs):return '['+','.join(map(str,xs))+']'
    s=['import M44Safety','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace BB6.Agent25M44',f'def headData : Array Nat := {arr(map(str,g["head"]))}',f'def startData : Array Nat := {arr(map(str,p[:n]))}',f'def nextData : Array (List (Nat × Nat)) := {arr("["+",".join(f"({a},{b})" for a,b in row)+"]" for row in g["delta"])}',f'def prevData : Array (List Nat) := {arr(lst(row) for row in prev)}',f'def edgeData : Array (Array (List Nat)) := #[\n'+',\n'.join(arr(lst(row) for row in qs) for qs in edges)+'\n]',f'''def cert : Cert where
  n := {n}
  head := fun s => headData.getD s 0
  next := fun s a => ((nextData.getD s []).find? (fun p => p.1==a)).map Prod.snd
  prev := fun s => prevData.getD s []
  start := fun s => startData.getD s 0
  edges := fun p x => (edgeData.getD p #[]).getD x []
  final := {final}
''', 'end BB6.Agent25M44']
    Path(path).write_text('\n'.join(s)+'\n')
    print('quotient states',len(edges),'edges',sum(len(r) for qs in edges for r in qs),'final',final,'path',path,flush=True)

if __name__=='__main__':
    import sys
    root=Path(__file__).resolve().parent
    emit(json.loads((root/'graph.json').read_text()),sys.argv[1] if len(sys.argv)>1 else root/'M44Data.lean')
