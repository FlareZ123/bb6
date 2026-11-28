from pathlib import Path
from collections import deque
from itertools import groupby
import json
H='''import Raw40Nores
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open BB6Coverage BB6Coverage.Agent50Zipper BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial BB6.Agent47CanonicalFrontier
'''
def lword(xs):
    a=[]
    for k,g in groupby(xs):
        n=len(list(g)); b=str(bool(k)).lower()
        a.append(f'List.replicate {n} {b}' if n>=5 else '['+','.join([b]*n)+']')
    return '('+' ++ '.join(a)+')' if a else '[]'
def emit(i,t,n,s,chunk=2048):
    from emit_symbolic import table
    a=t.replace('_','');tr=[a[j:j+3] for j in range(0,36,3)];l=deque();r=deque();q=h=0
    ns=f'BB6.Agent4Raw56LBLong.M{i}'
    z=lambda: f'⟨{q},({h}),{lword(l)},{lword(r)}⟩'
    out=[H,f'namespace {ns}',table(t),'def z0 : Z := Agent31Pump.start']; parts=[]
    for k in range(n):
        a=tr[q*2+(l[0] if l else 0)];assert a!='---'; w=int(a[0]);q=ord(a[2])-65
        if l:l.popleft()
        if a[1]=='R':l.appendleft(w);l.appendleft(r.popleft() if r else 0);h+=1
        else:r.appendleft(w);h-=1
        if (k+1)%chunk==0 or k+1==n:
            j=len(parts)+1; sz=(k+1)-sum(parts);parts.append(sz)
            out.extend([f'def z{j} : Z := {z()}',f'theorem p{j} : zrun table {sz} z{j-1} = some z{j} := by rfl'])
    assert tr[q*2+(l[0] if l else 0)]=='---' and q*2+(l[0] if l else 0)==s
    def join(a,b):
        if a+1==b:return parts[a],f'p{b}'
        m=(a+b)//2;n1,h1=join(a,m);n2,h2=join(m,b);name=f'j{a}_{b}'
        out.append(f'theorem {name} : zrun table {n1+n2} z{a} = some z{b} := by\n  rw [show {n1+n2} = {n1} + {n2} by rfl, zrun_add, {h1}, Option.bind_some, {h2}]');return n1+n2,name
    _,j=join(0,len(parts))
    out.append(f'''theorem check : prefixCheck 1000000 table (.last {n} ({s//2},{str(bool(s%2)).lower()})) = true := by
  unfold prefixCheck
  rw [checkAt.eq_1]
  have ha : advance table 0 Agent31Pump.start {n} = some z{len(parts)} := {j}
  rw [ha]
  rfl
theorem bound_quotient (m : Machine) (hm : TNFQuotientCompatible table m) : WeightedBound 1000000 m := by
  have hno : weightedTNFNoAssignedHalt table := by
    intro s; rcases s with ⟨q,b⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide
  rcases canonicalSound 1000000 table 6 (.closed (.last {n} ({s//2},{str(bool(s%2)).lower()}))) (by decide) (supportOK_sound _ _ (by decide)) (by decide) hno check m hm with hb | ⟨e,he,_⟩
  · exact hb
  · simp only [canonicalResiduals.eq_2,List.not_mem_nil] at he
#print axioms check
#print axioms bound_quotient
end {ns}''')
    return '\n'.join(out)+'\n'
