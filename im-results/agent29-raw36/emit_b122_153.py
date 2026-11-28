"""Three-phase growth of the exact F1-open Raw36 B1=1RE leaf 153.
The opaque suffix T is arbitrary. Every finite step and transfer is kernel checked.
"""
from pathlib import Path
import sys
import discover_sweep as ds
em=ds.em
TABLE='1RB1LE_1RC1RE_0RD1RF_0LD1LB_1LD0RE_0RA---'.replace('_','')
ACTIONS=[[[1,14,1,'01111',7],43,[0,18,0,'00010',41],157],[[1,19,1,'01111',7],62,[0,19,0,'00100',41],158],[[1,19,1,'01111',7],178,[0,21,0,'10000',41],160]]
STARTS=[(0,['0011'],['0010'+'00010'*k,'00010',w+'?']) for k,w in [(2,'000001000010101'),(3,'101000010101'),(3,'01011000010101'),(3,'0000010000101011')]]
NS='BB6.Agent29Raw36B122Phase153'
def expr(a):
    out=[]
    for i,x in enumerate(a):
        if not x:continue
        if i%2:assert '?' not in x;out.append(f'rep {em.lit(x)} n');continue
        if '?' in x:
            assert i==len(a)-1 and x.endswith('?') and x.count('?')==1
            if x[:-1]:out.append(em.lit(x[:-1]))
            out.append('T')
        else:out.append(em.lit(x))
    return ' ++ '.join(out) or '[]'
def ze(z):return f'⟨{z[0]}, {expr(z[1])}, {expr(z[2])}⟩'
def generate(path):
    p=[TABLE[j:j+3] for j in range(0,36,3)]
    out=[em.HEADER.format(ns=NS).replace('import SweepPumping','import ClosedGrowth'),'open BB6.Agent29ClosedGrowth',em.table(TABLE)]
    for i,z in enumerate(STARTS[:3]):out.append(f'def phase{i} (n : Nat) (T : List Bool) : Z0 := {ze(z)}')
    for i,(start,goal,acts) in enumerate(zip(STARTS,STARTS[1:],ACTIONS)):
        z=start;costs=[];c0=c1=0;out.append(f'namespace Phase{i}')
        for j,a in enumerate(acts):
            if isinstance(a,int):
                z1=z
                for _ in range(a):z1=em.step(p,z1)
                c0+=a;costs.append(str(a));out.append(f'theorem h{j} (n : Nat) (T : List Bool) : run0 table {a} {ze(z)} = some {ze(z1)} := by rfl')
            else:
                side,apl,bpl,o,k=a;q,l,r=z;src,dst=(l,r) if side==0 else (r,l);ap,w,*at=src;assert len(ap)==apl
                bp,bt=dst[0][:bpl],[dst[0][bpl:]]+dst[1:];assert len(bp)==bpl and len(w)==len(o)
                aa=em.pre(ap,at);bb=[bp,o]+bt;z1=(q,aa,bb) if side==0 else (q,bb,aa)
                lp,rp=(ap,bp) if side==0 else (bp,ap);L,R=(at,bt) if side==0 else (bt,at)
                l0,r0,I,O=map(em.lit,(lp,rp,w,o));assert all('?' not in x for x in (lp,rp,w,o))
                if side==0:
                    src=f'⟨{q}, {l0} ++ {I} ++ L, {r0} ++ R⟩';dst=f'⟨{q}, {l0} ++ L, {r0} ++ {O} ++ R⟩';fn='sweepL'
                else:
                    src=f'⟨{q}, {l0} ++ L, {r0} ++ {I} ++ R⟩';dst=f'⟨{q}, {l0} ++ {O} ++ L, {r0} ++ R⟩';fn='sweepR'
                c1+=k;costs.append(f'{k}*n');out.append(f'theorem one{j} (L R : List Bool) : run0 table {k} {src} = some {dst} := by rfl')
                out.append(f'theorem h{j} (n : Nat) (T : List Bool) : run0 table ({k}*n) {ze(z)} = some {ze(z1)} := by\n  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using ({fn} table {q} {l0} {r0} {I} {O} {k} one{j} n ({expr(L)}) ({expr(R)}))')
            z=z1
        assert z[0]==goal[0];out.append(f'theorem endEq (n : Nat) (T : List Bool) : ({ze(z)} : Z0) = {ze(goal)} := by');hs=[]
        for j,(a,b) in enumerate(zip(z[1:],goal[1:])):
            if a==b:continue
            hn='hl' if j==0 else 'hr';hs.append(hn);out.append(f'  have {hn} : {expr(a)} = {expr(b)} := by');trs=em.equal_transforms(a,b);names=[]
            for ti,(old,new,k,d,w,v,rev) in enumerate(trs):
                name=f'{hn}{ti}';names.append(name);out.append(f'    have {name} : {expr(old)} = {expr(new)} := by');a,b=old,new
                if rev:a,b=new,old;out.append('      symm')
                prefix=expr(a[:k]+[b[k]]);suffix=expr(a[k+2:]);out.append(f'      simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (commute_context ({prefix}) ({suffix}) {em.lit(d)} {em.lit(w)} {em.lit(v)} (by decide) n)')
            out.append('    exact '+names[0]+''.join(f'.trans {x}' for x in names[1:]) if names else '    rfl')
        out.append('  rw ['+','.join(hs)+']' if hs else '  rfl')
        cost=f'{c1}*n+{c0}';target=f'phase{i+1} n T' if i<2 else 'phase0 (n+1) (true::T)'
        out.append(f'theorem goalEq (n : Nat) (T : List Bool) : ({ze(goal)} : Z0) = {target} := by')
        if i<2:out.append('  rfl')
        else:out.append('  simp only [phase0,rep,List.append_assoc,List.cons_append]\n  rfl')
        out.append(f'theorem advance (n : Nat) (T : List Bool) : run0 table ({cost}) (phase{i} n T) = some ({target}) := by\n  have h := h0 n T')
        for j in range(1,len(acts)):out.append(f'  have h := join0 h (h{j} n T)')
        out.append(f'  rw [endEq,goalEq] at h\n  change run0 table _ (phase{i} n T) = _ at h\n  rw [show {cost} = '+ ' + '.join(costs)+' by omega]\n  exact h\nend Phase'+str(i))
    out.append('''theorem growth (n : Nat) (T : List Bool) : run0 table (144*n+758) (phase0 n T) = some (phase0 (n+1) (true::T)) := by
  have h := join0 (join0 (Phase0.advance n T) (Phase1.advance n T)) (Phase2.advance n T)
  rw [show 144*n+758=48*n+200+(48*n+220)+(48*n+338) by omega]
  exact h

def family (n : Nat) : Z0 := phase0 n (rep [true] n)
theorem entry : run0 table 1207 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1207 (fun n => 144*n+758) entry (by intro n; omega)
    (by intro n; simpa only [family,rep,List.singleton_append] using growth n (rep [true] n)) m hm
#print axioms growth
#print axioms never
end '''+NS)
    Path(path).write_text('\n'.join(out)+'\n')
if __name__=='__main__':generate(sys.argv[1])
