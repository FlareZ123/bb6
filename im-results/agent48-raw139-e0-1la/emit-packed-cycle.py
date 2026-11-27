#!/usr/bin/env python3
"""Exact packed replay for Raw139 OneLA leaf 11147. Every chunk is kernel checked.
No search: same known entry, period and retained side as emit-long-cycle.py.
"""
import pathlib,sys
P=[7,20,11,7,14,1,24,16,2,11,8,4]
E,N,B=139556,1352801,996
CHUNK=4000
HEADER='set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nnamespace BB6.Agent48OneLAPacked\nopen BB6Coverage BB6.Agent3PackedCycle\n'
END='end BB6.Agent48OneLAPacked\n'

def trajectory():
    q=h=l=r=0
    times=set(range(CHUNK,E,CHUNK))|{0,E}|set(range(E+CHUNK,E+N,CHUNK))|{E+N}
    for t in range(E+N+1):
        if t in times: yield t,q,h,l,r
        if t==E+N: break
        if t>=E: assert h>=B
        v=P[2*q+l%2];assert v!=24
        w=v//2%2;q=v//4
        if v%2:
            h+=1;l=r%2+2*w+4*(l//2);r//=2
        else:
            h-=1;l//=2;r=w+2*r

def main(out):
    out.mkdir(parents=True,exist_ok=True)
    tr=list(trajectory())
    a=next(x for x in tr if x[0]==E);c=tr[-1]
    assert a[1]==c[1] and c[2]-a[2]==11187
    assert a[4]==c[4] and a[3]%(2**(a[2]-B+1))==c[3]%(2**(a[2]-B+1))
    cfg='import OneLAPackedCore\n'+HEADER
    for t,q,h,l,r in tr:
        cfg+=f'def z{t} : H := '+('startH' if t==0 else f'⟨⟨{q},{l},{r}⟩,({h})⟩')+'\n'
    (out/'OneLAPackedConfigs.lean').write_text(cfg+END)
    pairs=[(a[0],b[0]) for a,b in zip(tr,tr[1:])]
    modules=[]
    for i in range(0,len(pairs),4):
        name=f'OneLAPackedStep{i//4:03}'
        modules.append(name)
        s='import OneLAPackedConfigs\n'+HEADER
        for t,u in pairs[i:i+4]:
            flag='false' if t<E else 'true'
            s+=f'theorem h{t}_{u} : runFast {flag} {u-t} z{t} = some z{u} := by decide +kernel\n'
        (out/(name+'.lean')).write_text(s+END)
    lines=[]
    def join(xs,flag):
        if len(xs)==1:return f'h{xs[0][0]}_{xs[0][1]}'
        m=len(xs)//2;l=join(xs[:m],flag);r=join(xs[m:],flag)
        t,v,u=xs[0][0],xs[m][0],xs[-1][1]
        name=f'agg{t}_{u}'
        lines.append(f'theorem {name} : runFast {flag} {u-t} z{t} = some z{u} := @runFast_join {flag} {v-t} {u-v} z{t} z{v} z{u} {l} {r}')
        return name
    he=join([x for x in pairs if x[0]<E],'false')
    hl=join([x for x in pairs if x[0]>=E],'true')
    s=''.join('import '+m+'\n' for m in modules)+HEADER+'\n'.join(lines)+'\n'
    s+=f'''theorem tail : tailH true {B} z{E} z{E+N} = true := by decide +kernel
theorem checked : cycleH ctr {E} {N} true {B} = true := mkCycle {he} {hl} tail
#print axioms checked
'''+END
    s+=f'''namespace BB6.Agent48OneLALongCycle
open BB6Coverage BB6.Agent3PackedCycle
def ctr : PartialMachine := BB6.Agent48OneLAPacked.ctr
theorem checked : cycleH ctr {E} {N} true {B} = true := BB6.Agent48OneLAPacked.checked
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  cycleH_sound ctr {E} {N} true {B} (by decide) checked m hm
#print axioms never
end BB6.Agent48OneLALongCycle
'''
    (out/'OneLALongCycle.lean').write_text(s)
    (out/'shard-modules.txt').write_text('\n'.join(modules)+'\n')
    print('Generated',len(pairs),'packed replay chunks in',len(modules),'modules; shift',c[2]-a[2])

if __name__=='__main__':main(pathlib.Path(sys.argv[1]))
