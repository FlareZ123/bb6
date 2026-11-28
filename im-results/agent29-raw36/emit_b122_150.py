"""Two-phase counter growth with an arbitrary finite suffix; all transitions checked in Lean."""
from pathlib import Path
import sys
import discover_sweep as ds
em=ds.em
TABLE='1RB1LE_1RC1RE_0RD0RF_0LD1LB_1LD0RE_1RA---'.replace('_','')
NS='BB6.Agent29Raw36B122Phase150'
X=(0,['0101'],['0100010',('0010','n'),'0100?'])
Y=(0,['0101'],['01000100010',('0010','n'),'11?'])
Y2=(0,['0101'],['0100010',('0010','n'),'11',('1','k'),'0?'])
X2=(0,['0101'],['0100010',('0010','n'),'0100',('0','k'),'1?'])
Y3=(0,['0101'],['0100010',('0010','n'),'11',('1','k'),''])
X3=(0,['0101'],['0100010',('0010','n'),'0100',('0','k'),'1'])
XY=[[1,7,1,'1011',4,'n'],31,[0,10,0,'0010',30,'n'],83]
YX=[[1,7,1,'1011',4,'n'],9,[1,2,1,'0',1,'k'],4,[0,3,0,'0',1,'k'],23,[0,7,0,'0100',30,'n'],54]

def expr(a):
    out=[]
    for i,x in enumerate(a):
        if not x:continue
        if i%2:
            w,v=x;assert '?' not in w;out.append(f'rep {em.lit(w)} {v}');continue
        if '?' in x:
            assert i==len(a)-1 and x.endswith('?') and x.count('?')==1
            if x[:-1]:out.append(em.lit(x[:-1]))
            out.append('T')
        else:out.append(em.lit(x))
    return ' ++ '.join(out) or '[]'
def ze(z):return f'⟨{z[0]}, {expr(z[1])}, {expr(z[2])}⟩'
def strip(a):return [x[0] if i%2 else x for i,x in enumerate(a)]
def tagged(a,old):return [x if i%2==0 else (x,old[i][1]) for i,x in enumerate(a)]

def emit_phase(name,start,goal,acts,params,cost,target,source):
    p=[TABLE[j:j+3] for j in range(0,36,3)];z=start;costs=[];out=[f'namespace {name}'];args=' '.join(v for v in ('n','k','T') if f'({v} :' in params)
    for j,a in enumerate(acts):
        if isinstance(a,int):
            z1=z
            for _ in range(a):z1=em.step(p,z1)
            costs.append(str(a));out.append(f'theorem h{j} {params} : run0 table {a} {ze(z)} = some {ze(z1)} := by rfl')
        else:
            side,apl,bpl,o,k,v=a;q,l,r=z;src,dst=(l,r) if side==0 else (r,l);ap,(w,v0),*at=src;assert v0==v and len(ap)==apl
            bp,bt=dst[0][:bpl],[dst[0][bpl:]]+dst[1:];assert len(bp)==bpl and len(w)==len(o)
            aa=em.pre(ap,at);bb=[bp,(o,v)]+bt;z1=(q,aa,bb) if side==0 else (q,bb,aa)
            lp,rp=(ap,bp) if side==0 else (bp,ap);L,R=(at,bt) if side==0 else (bt,at);l0,r0,I,O=map(em.lit,(lp,rp,w,o));assert all('?' not in x for x in (lp,rp,w,o))
            if side==0:
                src=f'⟨{q}, {l0} ++ {I} ++ L, {r0} ++ R⟩';dst=f'⟨{q}, {l0} ++ L, {r0} ++ {O} ++ R⟩';fn='sweepL'
            else:
                src=f'⟨{q}, {l0} ++ L, {r0} ++ {I} ++ R⟩';dst=f'⟨{q}, {l0} ++ {O} ++ L, {r0} ++ R⟩';fn='sweepR'
            costs.append(f'{k}*{v}');out.append(f'theorem one{j} (L R : List Bool) : run0 table {k} {src} = some {dst} := by rfl')
            out.append(f'theorem h{j} {params} : run0 table ({k}*{v}) {ze(z)} = some {ze(z1)} := by\n  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using ({fn} table {q} {l0} {r0} {I} {O} {k} one{j} {v} ({expr(L)}) ({expr(R)}))')
        z=z1
    assert z[0]==goal[0];out.append(f'theorem endEq {params} : ({ze(z)} : Z0) = {ze(goal)} := by');hs=[]
    for j,(a,b) in enumerate(zip(z[1:],goal[1:])):
        if a==b:continue
        hn='hl' if j==0 else 'hr';hs.append(hn);out.append(f'  have {hn} : {expr(a)} = {expr(b)} := by')
        assert [x[1] for x in a[1::2]]==[x[1] for x in b[1::2]]
        trs=em.equal_transforms(strip(a),strip(b));names=[]
        for ti,(old,new,k,d,w,v,rev) in enumerate(trs):
            old,new=tagged(old,a),tagged(new,a);par=old[k+1][1];eqname=f'{hn}{ti}';names.append(eqname);out.append(f'    have {eqname} : {expr(old)} = {expr(new)} := by');a0,b0=old,new
            if rev:a0,b0=new,old;out.append('      symm')
            prefix=expr(a0[:k]+[b0[k]]);suffix=expr(a0[k+2:]);out.append(f'      simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (commute_context ({prefix}) ({suffix}) {em.lit(d)} {em.lit(w)} {em.lit(v)} (by decide) {par})')
        out.append('    exact '+names[0]+''.join(f'.trans {x}' for x in names[1:]) if names else '    rfl')
    out.append('  rw ['+','.join(hs)+']' if hs else '  rfl')
    out.append(f'theorem goalEq {params} : ({ze(goal)} : Z0) = {target} := by\n  simp only [phaseX,phaseY,rep,List.append_assoc,List.cons_append,List.append_nil,List.nil_append] <;> rfl')
    out.append(f'theorem advance {params} : run0 table ({cost}) ({source}) = some ({target}) := by\n  have h := h0 {args}')
    for j in range(1,len(acts)):out.append(f'  have h := join0 h (h{j} {args})')
    out.append(f'  rw [endEq,goalEq] at h\n  rw [show {cost} = '+ ' + '.join(costs)+' by omega]\n  simpa only [phaseX,phaseY,List.append_assoc,List.cons_append,List.append_nil,List.nil_append] using h\nend '+name)
    return '\n'.join(out)

def generate(path):
    out=[em.HEADER.format(ns=NS).replace('import SweepPumping','import ClosedGrowth'),'open BB6.Agent29ClosedGrowth',em.table(TABLE),f'def phaseX (n : Nat) (T : List Bool) : Z0 := {ze(X)}',f'def phaseY (n : Nat) (T : List Bool) : Z0 := {ze((0,["0101"],["0100010",("0010","n"),"11?"]))}']
    out.append(emit_phase('XY',X,Y,XY,'(n : Nat) (T : List Bool)','34*n+114','phaseY (n+1) T','phaseX n T'))
    out.append(emit_phase('YXZero',Y2,X2,YX,'(n : Nat) (k : Nat) (T : List Bool)','34*n+2*k+90','phaseX n (rep [false] k ++ true::T)','phaseY n (rep [true] k ++ false::T)'))
    out.append(emit_phase('YXBlank',Y3,X3,YX,'(n : Nat) (k : Nat)','34*n+2*k+90','phaseX n (rep [false] k ++ [true])','phaseY n (rep [true] k)'))
    out.append('''theorem firstZero (T : List Bool) : (∃ k, T = rep [true] k) ∨ (∃ k U, T = rep [true] k ++ false::U) := by
  induction T with
  | nil => exact Or.inl ⟨0,rfl⟩
  | cons b T ih =>
    cases b with
    | false => exact Or.inr ⟨0,T,rfl⟩
    | true =>
      rcases ih with ⟨k,h⟩ | ⟨k,U,h⟩
      · exact Or.inl ⟨k+1,by rw [h]; rfl⟩
      · exact Or.inr ⟨k+1,U,by rw [h]; rfl⟩

inductive inv : Z0 → Prop where
  | x (n : Nat) (T : List Bool) : inv (phaseX n T)
  | y (n : Nat) (T : List Bool) : inv (phaseY n T)

theorem next (z : Z0) (hz : inv z) : ∃ t z', 0<t ∧ run0 table t z = some z' ∧ inv z' := by
  cases hz with
  | x n T => exact ⟨34*n+114,phaseY (n+1) T,by omega,XY.advance n T,inv.y _ _⟩
  | y n T =>
    rcases firstZero T with ⟨k,rfl⟩ | ⟨k,U,rfl⟩
    · exact ⟨34*n+2*k+90,phaseX n (rep [false] k ++ [true]),by omega,YXBlank.advance n k,inv.x _ _⟩
    · exact ⟨34*n+2*k+90,phaseX n (rep [false] k ++ true::U),by omega,YXZero.advance n k U,inv.x _ _⟩

theorem entry : run0 table 221 ⟨0,[],[]⟩ = some (phaseY 1 []) := by rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_invariant table inv 221 (phaseY 1 []) entry (inv.y 1 []) next m hm
#print axioms XY.advance
#print axioms YXZero.advance
#print axioms YXBlank.advance
#print axioms never
end '''+NS)
    Path(path).write_text('\n'.join(out)+'\n')
if __name__=='__main__':generate(sys.argv[1])
