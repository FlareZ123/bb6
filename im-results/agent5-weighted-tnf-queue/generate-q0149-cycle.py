"""Replay three exact shared five-phase nonhalting certificates. No search.
python generate-q0149-cycle.py OUTDIR
Uses the kernel-checked SweepPumping lemmas and exact finite paths.
"""
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'agent48-raw139-f1-oneLA'))
import emitproof as E
from autopump import G, normalize, step, pump
E.expr=lambda xs,n='n': ' ++ '.join(E.bits(x) if isinstance(x,str) else x.p if x.p in ('L','R') else f'rep {E.bits(x.p)} {n}' for x in xs) or '[]'
PHASES=[(2,1,1),(4,3,1),(4,7,3),(6,9,5),(10,13,1),(10,17,1)]
RECIPES={
11:['2 R1:2 27 L2:14 13',
'2 R1:16 17 L2:112 14 R1:16 7 L1:16 26 L2:56 1',
'4 R1:16 47 L2:112 30 R1:16 11 L0:16 28 L2:56 1',
'6 R1:16 63 L2:112 46 R1:16 11 L0:16 44 L2:56 1',
'10 R1:16 25 L2:112 78 R1:16 35 L2:112 70 R1:16 13 L0:16 75 L2:56 1',
'16 R1:16 17 L2:112 126 R1:16 7 L0:16 82 L2:56 1'],
16:['2 R1:2 21 L2:10 11',
'2 R1:16 13 L2:80 12 R1:16 7 L0:16 18 L2:40 1',
'4 R1:16 37 L2:80 24 R1:16 11 L0:16 20 L2:40 1',
'6 R1:16 49 L2:80 36 R1:16 11 L0:16 32 L2:40 1',
'10 R1:16 21 L2:80 60 R1:16 27 L2:80 54 R1:16 13 L0:16 55 L2:40 1',
'16 R1:16 13 L2:80 96 R1:16 7 L0:16 62 L2:40 1']}
TABLES={11:[7,10,11,20,0,13,3,19,22,15,24,4],16:[7,10,11,24,0,13,3,19,22,15,10,20],17:[7,10,11,24,0,13,3,19,22,15,11,20]}
RECIPES[17]=RECIPES[11]
bits=E.bits

def emit_run(name,p,start,target,recipe,binders='(n : Nat)'):
    a=start; groups=[]
    for token in recipe.split():
        if token.isdigit():
            k=int(token); x=a
            for _ in range(k):
                a=step(p,a)
                assert a is not None
            groups.append(('fin',k,x,a))
        else:
            side=token[0]; j,k=map(int,token[1:].split(':'))
            matches=[(b,op) for b,op in pump(p,a,side) if len(op[3])==j and op[6]==k]
            assert len(matches)==1,(name,token,matches)
            b,op=matches[0];groups.append(('pump',a,b,op));a=b
    assert a[0]==target[0]
    c=sum(g[1] for g in groups if g[0]=='fin')
    d=sum(g[3][6] for g in groups if g[0]=='pump')
    cost=f'{d}*n+{c}'
    out=[f'theorem {name} {binders} : run0 ctr ({cost}) {E.zexpr(start)} = some {E.zexpr(target)} := by']
    costs=[];hs=[]
    for j,g in enumerate(groups):
        h=f'h{j}';hs.append(h)
        if g[0]=='fin':
            _,k,x,y=g;costs.append(str(k));out.append(f'  have {h} : run0 ctr {k} {E.zexpr(x)} = some {E.zexpr(y)} := rfl')
        else:
            _,x,y,op=g;side,q,sp,dp,P,O,k,sr,dr=op;costs.append(f'{k}*n')
            if side=='L':lp,rp,L,R=sp,dp,sr,dr
            else:lp,rp,L,R=dp,sp,dr,sr
            out.append(f'  have {h} : run0 ctr ({k}*n) {E.zexpr(x)} = some {E.zexpr(y)} := by')
            out.append(f'    simpa only [List.append_assoc, List.nil_append, List.append_nil, List.cons_append] using sweep{side} ctr {q} {bits(lp)} {bits(rp)} {bits(P)} {bits(O)} {k} (by intro L R; rfl) n ({E.expr(L)}) ({E.expr(R)})')
    out.append(f'  have H := {hs[0]}')
    for h in hs[1:]:out.append(f'  have H := join0 H {h}')
    out.append(f'  have hcost : {"+".join(costs)} = {cost} := by omega')
    out.append('  rw [hcost] at H')
    if a!=target:
        out.append(f'  have hlast : ({E.zexpr(a)} : Z0) = {E.zexpr(target)} := by')
        out.append('    congr 1')
        for w,v in zip(a[1:],target[1:]):
            if w!=v:out.extend(E.equality(w,v,'    '))
        out.append('  rw [hlast] at H')
    out.append('  exact H')
    return '\n'.join(out),cost

def phase(a,b,c):
    return (0,(),normalize(['010'+'1'*a,G('1'*8),'0'*(b//4*4),G('0'*16),'0'*(b%4)+'1'*c]))

def generate(i):
    ns=f'BB6.Agent50Q0149H{i}';p=TABLES[i]
    out=['import SweepPumping','import FastFAR','import WeightedTNF','set_option maxRecDepth 100000','set_option maxHeartbeats 0',f'namespace {ns}','open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent13BlankDelay',f'def ctr : PartialMachine := FAR.fromCodes {p}']
    inner=(2,('1011',G('L')),('11',G('11'),'0000',G('R')))
    target=(2,('101111',G('L')),('1111',G('11'),G('R')))
    s,cost=emit_run('inner',p,inner,target,RECIPES[i][0],'(n : Nat) (L R : List Bool)')
    out.append(s)
    costs=[]
    for j,((a,b,c),(A,B,C)) in enumerate(zip(PHASES,PHASES[1:])):
        k,b0=divmod(b,4)
        start=(2,normalize(['10'+'1'*(2+2*k),G('1'*8)]),normalize(['1'*(a+2*k),G('1'*16),'0'*b0+'1'*c]))
        s,t=emit_run(f'tail{j}',p,start,phase(A,B,C),RECIPES[i][j+1]);out.append(s);costs.append(t)
    out.append(TEMPLATE.replace('COST',cost.replace('n','u')))
    for j,(a,b,c) in enumerate(PHASES):out.append(f'def phase{j} (n : Nat) : Z0 := {E.zexpr(phase(a,b,c))}')
    for j,((a,b,c),(A,B,C)) in enumerate(zip(PHASES,PHASES[1:])):
        u=a//2-1;k,b0=divmod(b,4);R=bits('0'*b0+'1'*c)
        out.append(f"""
private theorem phaseStep{j} (n : Nat) : ∃ t, 0 < t ∧ run0 ctr t (phase{j} n) = some (phase{j+1} n) := by
  let u := {u}+4*n
  let k := {k}+4*n
  let R : List Bool := {R}
  have h0 : run0 ctr 5 (phase{j} n) = some ⟨2,[true,false,true,true],[true,true]++rep [true,true] u++rep [false,false,false,false] k++R⟩ := by
    simp only [phase{j},u,k,R,repAdd,repMul,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil]
    rfl
  obtain ⟨t,ht⟩ := consume u k [] R
  have hh := join0 h0 ht
  have ht2 := tail{j} n
  have h' : run0 ctr (5+t) (phase{j} n) = some ⟨2,{bits('10'+'1'*(2+2*k))} ++ rep {bits('1'*8)} n,{bits('1'*(a+2*k))} ++ rep {bits('1'*16)} n ++ {R}⟩ := by
    have he : u+k = {u+k}+8*n := by dsimp [u,k]; omega
    rw [he] at hh
    simpa only [u,k,R,repAdd,repMul,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using hh
  refine ⟨5+t+({costs[j]}),by omega,?_⟩
  simpa only [phase{j+1},List.nil_append,List.append_assoc] using join0 h' ht2
""")
    entry=28 if i==16 else 34
    out.append(f"""
theorem seed : run0 ctr {entry} ⟨0,[],[]⟩ = some (phase0 0) := rfl
theorem cycle (n : Nat) : ∃ t, 0 < t ∧ run0 ctr t (phase0 n) = some (phase0 (n+1)) := by
  obtain ⟨t0,p0,h0⟩ := phaseStep0 n
  obtain ⟨t1,p1,h1⟩ := phaseStep1 n
  obtain ⟨t2,p2,h2⟩ := phaseStep2 n
  obtain ⟨t3,p3,h3⟩ := phaseStep3 n
  obtain ⟨t4,p4,h4⟩ := phaseStep4 n
  refine ⟨t0+t1+t2+t3+t4,by omega,?_⟩
  have H := join0 (join0 (join0 (join0 h0 h1) h2) h3) h4
  have he : phase5 n = phase0 (n+1) := by simp only [phase5,phase0,rep,List.append_assoc,List.nil_append,List.cons_append]
  rw [he] at H
  exact H
noncomputable def cost (n : Nat) := Classical.choose (cycle n)
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  never_of_growth ctr phase0 {entry} cost seed (fun n => (Classical.choose_spec (cycle n)).1) (fun n => (Classical.choose_spec (cycle n)).2) m hm
theorem cover (B : Nat) : Cover (WeightedBound B) ctr :=
  .leaf _ fun m hm => weighted_never B m (never m hm)
#print axioms never
#print axioms cover
end {ns}
""")
    return '\n\n'.join(out)

TEMPLATE="""
private theorem repAdd (P : List Bool) (n k : Nat) : rep P (n+k) = rep P n ++ rep P k := by
  induction n with
  | zero => simp [rep]
  | succ n ih => rw [show n+1+k = n+k+1 by omega]; simp only [rep,ih,List.append_assoc]
private theorem repMul (P : List Bool) (k n : Nat) : rep P (k*n) = rep (rep P k) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.mul_succ, repAdd, ih, rep, rep_snoc]

private theorem consume (u k : Nat) (L R : List Bool) :
    ∃ t, run0 ctr t ⟨2,[true,false,true,true]++L,[true,true]++rep [true,true] u++rep [false,false,false,false] k++R⟩ =
    some ⟨2,[true,false,true,true]++rep [true,true] k++L,[true,true]++rep [true,true] (u+k)++R⟩ := by
  induction k generalizing u L with
  | zero => exact ⟨0,by simp [rep,run0]⟩
  | succ k ih =>
    have h := inner u L (rep [false,false,false,false] k++R)
    have h1 : run0 ctr (COST) ⟨2,[true,false,true,true]++L,[true,true]++rep [true,true] u++rep [false,false,false,false] (k+1)++R⟩ =
      some ⟨2,[true,false,true,true]++([true,true]++L),[true,true]++rep [true,true] (u+1)++rep [false,false,false,false] k++R⟩ := by
      simpa only [rep,List.append_assoc,List.cons_append,List.nil_append] using h
    obtain ⟨t,ht⟩ := ih (u+1) ([true,true]++L)
    refine ⟨(COST)+t,?_⟩
    have hh := join0 h1 ht
    rw [show u+1+k = u+(k+1) by omega] at hh
    have hleft : [true,false,true,true]++rep [true,true] k++([true,true]++L) = [true,false,true,true]++rep [true,true] (k+1)++L := by
      rw [rep]
      simp only [List.append_assoc]
      rw [← List.append_assoc (rep [true,true] k) [true,true] L, rep_snoc [true,true] k, List.append_assoc]
    rw [hleft] at hh
    exact hh
"""
if __name__=='__main__':
    out=Path(sys.argv[1]);out.mkdir(parents=True,exist_ok=True)
    for i in TABLES:(out/f'Q0149H{i}.lean').write_text(generate(i))

