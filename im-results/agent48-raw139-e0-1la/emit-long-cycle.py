"""Untrusted exact replay generator for the long translated cycle 11147.
Every emitted chunk and the retained-tail equality are kernel-checked.
"""
from pathlib import Path
from collections import deque
import sys
P=[7,20,11,7,14,1,24,16,2,11,8,4]
E,N,B=139556,1352801,996

def trajectory(chunk):
    q=h=0;L=deque();R=deque()
    yield (0,q,h,[],[])
    times=set(range(chunk,E,chunk))|{E}|set(range(E+chunk,E+N,chunk))|{E+N}
    for t in range(1,E+N+1):
        if t-1>=E:assert h>=B
        a=L[0] if L else 0;v=P[2*q+a];assert v!=24
        w=v//2%2;q=v//4
        if L:L.popleft()
        if v%2:
            h+=1;L.appendleft(w);L.appendleft(R.popleft() if R else 0)
        else:
            h-=1;R.appendleft(w)
        if t in times:yield (t,q,h,list(L),list(R))

def bits(w):
    s=[]
    for i in range(0,len(w),64):
        x=w[i:i+64];v=sum(b<<j for j,b in enumerate(x));s.append(f'bits {v} {len(x)}')
    return '('+' ++ '.join(s)+')' if s else '[]'

def cfg(t,q,h,L,R):
    if t==0:return 'def z0 : Z := start\n'
    return f'def z{t} : Z := ⟨{q}, ({h}), {bits(L)}, {bits(R)}⟩\n'

core="""import ZipAuditCore
import FastThreeHoleAudit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent48OneLALongCycle
open BB6Coverage Agent50Zipper Agent50SideCycle Agent31Pump Agent10ZipAudit
open BB6Coverage.FAR
def ctr : PartialMachine := fromCodes [7,20,11,7,14,1,24,16,2,11,8,4]
def bits (v : Nat) : Nat → List Bool
 | 0 => []
 | n+1 => (v % 2 == 1) :: bits (v/2) n
theorem window_add (p : PartialMachine) (right : Bool) (b : Int) (n k : Nat) (z : Z) :
    zipWindow p right b (n+k) z = (zipWindow p right b n z).bind (zipWindow p right b k) := by
  induction n generalizing z with
  | zero => simp [zipWindow]
  | succ n ih =>
    rw [show n+1+k=n+k+1 by omega]
    by_cases h : side right b z.h
    · cases hs : step p z <;> simp [zipWindow,h,hs,ih]
    · simp [zipWindow,h]
theorem joinRun {a b c : Z} {n k : Nat} (ha : zrun ctr n a = some b) (hb : zrun ctr k b = some c) : zrun ctr (n+k) a = some c := by
  rw [zrun_add,ha,Option.bind_some,hb]
theorem joinWin {a b c : Z} {n k : Nat} (ha : zipWindow ctr true 996 n a = some b) (hb : zipWindow ctr true 996 k b = some c) : zipWindow ctr true 996 (n+k) a = some c := by
  rw [window_add,ha,Option.bind_some,hb]
theorem mkCycle (p : PartialMachine) (e n : Nat) (r : Bool) (b : Int) (c d : Z)
    (he : zrun p e start = some c) (hl : zipWindow p r b n c = some d) (ht : zipTailEq r b c d = true) : zipCycle p e n r b = true := by
  simp only [zipCycle, he, hl, ht]
end BB6.Agent48OneLALongCycle
"""
def generate(out,chunk=10000):
    out.mkdir(exist_ok=True,parents=True)
    (out/'OneLALongCore.lean').write_text(core)
    tr=list(trajectory(chunk))
    header='set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nnamespace BB6.Agent48OneLALongCycle\nopen BB6Coverage Agent50Zipper Agent50SideCycle Agent31Pump Agent10ZipAudit\n'
    end='end BB6.Agent48OneLALongCycle\n'
    (out/'OneLALongConfigs.lean').write_text('import OneLALongCore\n'+header+''.join(cfg(*x) for x in tr)+end)
    pairs=[(a[0],b[0]) for a,b in zip(tr,tr[1:])]
    modules=[]
    for i in range(0,len(pairs),4):
        name=f'OneLALongStep{i//4:03}'
        modules.append(name)
        s='import OneLALongConfigs\n'+header
        for t,u in pairs[i:i+4]:
            p='zrun ctr' if t<E else 'zipWindow ctr true 996'
            s+=f'theorem h{t}_{u} : {p} {u-t} z{t} = some z{u} := by decide +kernel\n'
        (out/(name+'.lean')).write_text(s+end)
    lines=[]
    def join(xs,kind):
        if len(xs)==1:return f'h{xs[0][0]}_{xs[0][1]}'
        m=len(xs)//2
        l=join(xs[:m],kind);r=join(xs[m:],kind)
        t,v,u=xs[0][0],xs[m][0],xs[-1][1]
        p='zrun ctr' if kind=='Run' else 'zipWindow ctr true 996'
        name=f'agg{t}_{u}'
        lines.append(f'theorem {name} : {p} {u-t} z{t} = some z{u} := @join{kind} z{t} z{v} z{u} {v-t} {u-v} {l} {r}')
        return name
    he=join([x for x in pairs if x[0]<E],'Run')
    hl=join([x for x in pairs if x[0]>=E],'Win')
    s=''.join('import '+m+'\n' for m in modules)+header+'\n'.join(lines)+'\n'
    s+=f"""theorem tail : zipTailEq true 996 z{E} z{E+N} = true := by decide +kernel
theorem checked : zipCycle ctr {E} {N} true 996 = true :=
  mkCycle ctr {E} {N} true 996 z{E} z{E+N} {he} {hl} tail
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  zipCycle_sound ctr {E} {N} true 996 (by decide) checked m hm
#print axioms checked
#print axioms never
"""
    (out/'OneLALongCycle.lean').write_text(s+end)
    print('Generated',len(pairs),'checked replay chunks and',len(modules),'modules')
if __name__=='__main__':generate(Path(sys.argv[1]))
