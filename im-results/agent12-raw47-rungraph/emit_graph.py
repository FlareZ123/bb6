import sys,pathlib

def a(xs):return '#['+','.join(map(str,xs))+']'
def l(xs):return '['+','.join(map(str,xs))+']'
def b(x):return str(bool(x)).lower()
def tree(items):
    items=list(items)
    if not items:return '.empty'
    if len(items)==1 and items[0][0]==0:return f'(.leaf {items[0][1]})'
    return '(.branch '+tree((i//2,v) for i,v in items if not i%2)+' '+tree((i//2,v) for i,v in items if i%2)+')'
lines=iter(open(sys.argv[1])); out=pathlib.Path(sys.argv[2]);out.mkdir(exist_ok=True,parents=True)
for line in lines:
    i,t=line.split();D=[];E=[];N=[]
    for _ in range(2):
        n=int(next(lines));d=[];e=[]
        for j in range(n):
            x=list(map(int,next(lines).split()));d+=x[:2];e.append(l(f'({b(x[k])},{x[k+1]})' for k in range(2,len(x),2)))
        N.append(n);D.append(tree((i,str(v)) for i,v in enumerate(d) if v));E.append(tree((i,v) for i,v in enumerate(e) if v!='[]'))
    n=int(next(lines));rows=[[[] for _ in range(N[0])] for _ in range(12)]
    for _ in range(n):
        s,u,v=map(int,next(lines).split());rows[s][u].append(v)
    for row in rows:
        while row and not row[-1]:row.pop()
    s=f'''import RunGraph
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent12Raw47.Run{i}
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent12RunGraph
def parent : PartialMachine := fromCodes {l(24 if t[j]=='-' else (ord(t[j+2])-65)*4+int(t[j])*2+int(t[j+1]=='R') for j in range(0,36,3))}
def cert : Cert := ⟨⟨{D[0]},{E[0]}⟩,⟨{D[1]},{E[1]}⟩,{a(tree((i,'⟨'+str(sum(1<<x for x in rs))+','+l(rs)+'⟩') for i,rs in enumerate(row) if rs) for row in rows)}⟩
theorem checked : check parent cert = true := by decide +kernel
theorem never (m : Machine) (hm : compatible parent m) : NeverHalts m := BB6.Agent12RunGraph.never checked m hm
theorem weighted (B : Nat) : Cover (WeightedBound B) parent := BB6.Agent12RunGraph.weighted checked B
#print axioms never
end BB6.Agent12Raw47.Run{i}
'''
    (out/f'Run{i}.lean').write_text(s)
