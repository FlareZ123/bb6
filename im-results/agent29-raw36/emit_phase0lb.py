"""Emit the twenty-phase Raw36 B1=0LB sweep cycle, checking exact symbolic transitions."""
import json,sys
from pathlib import Path
import discover_sweep as ds
em=ds.em
ROWS=[[2,"00000011000110",[[1,10,1,"10011",5],30,[0,7,0,"01100",13],29]],[1,"1100100110000011000110",[[1,5,1,"10011",5],10,[0,11,0,"00110",13],41]],[4,"0011000110",[[1,20,1,"10011",5],40,[0,17,0,"01100",13],55]],[3,"110010011011000110",[[1,15,1,"10011",5],20,[0,21,0,"00110",13],67]],[5,"11011000110",[[1,25,1,"10011",5],89,[0,28,0,"11000",13],82]],[6,"0001100100110",[[1,30,1,"10011",5],50,[0,27,0,"01100",13],81]],[5,"110010011001100100110",[[1,25,1,"10011",5],30,[0,31,0,"00110",13],93]],[7,"11001100100110",[[1,35,1,"10011",5],40,[0,41,0,"00110",13],119]],[8,"110100100110",[[1,40,1,"10011",5],138,[0,43,0,"11000",13],121]],[9,"00000000100110",[[1,45,1,"10011",5],65,[0,42,0,"01100",13],120]],[8,"1100100110000000100110",[[1,40,1,"10011",5],45,[0,46,0,"00110",13],132]],[11,"0000100110",[[1,55,1,"10011",5],75,[0,52,0,"01100",13],146]],[10,"110010011000100110",[[1,50,1,"10011",5],55,[0,56,0,"00110",13],158]],[13,"100110",[[1,65,1,"10011",5],69,[0,66,0,"00110",13],184]],[13,"110110110",[[1,65,1,"10011",5],133,[0,68,0,"11000",13],186]],[14,"00000100110",[[1,70,1,"10011",5],90,[0,67,0,"01100",13],185]],[13,"1100100110000100110",[[1,65,1,"10011",5],70,[0,71,0,"00110",13],197]],[16,"0100110",[[1,80,1,"10011",5],87,[0,82,0,"01100",13],224]],[16,"1100110110",[[1,80,1,"10011",5],85,[0,86,0,"00110",13],236]],[17,"11010110",[[1,85,1,"10011",5],201,[0,88,0,"11000",13],238]]]
def generate(outpath):
 s='1RB0RB_1RC0LB_0RD1RE_0LD1LB_1LD0RF_0RA---'.replace('_','');p=[s[j:j+3] for j in range(0,36,3)]
 NS='BB6.Agent29Raw36B1LBCycle'
 head=em.HEADER.format(ns=NS).replace('import SweepPumping','import ClosedGrowth')+'open BB6.Agent29ClosedGrowth\n'+em.table(s)+'\n'
 out=[head]
 starts=[(1,['01'],['11000'*a,'11000',w]) for a,w,_ in ROWS]
 recs=[(start,goal,row[2]) for start,goal,row in zip(starts,starts[1:]+[(1,['01'],['11000'*18,'11000',ROWS[0][1]])],ROWS)]
 for i,(a,b,acts) in enumerate(recs):out.append(f'def phase{i} (n : Nat) : Z0 := {em.ze(a)}')
 costs=[]
 for i,(start,goal,actions) in enumerate(recs):
  z=start;c0=c1=0;cost=[]
  out.append(f'namespace Phase{i}')
  for j,act in enumerate(actions):
   if isinstance(act,int):
    z1=z
    for _ in range(act):z1=em.step(p,z1)
    c0+=act;cost.append(str(act));out.append(f'theorem h{j} (n : Nat) : run0 table {act} {em.ze(z)} = some {em.ze(z1)} := by rfl')
   else:
    side,apl,bpl,o,k=act;q,l,r=z;a,b=(l,r) if side==0 else (r,l);ap,w,*at=a;assert len(ap)==apl
    bp,bt=b[0][:bpl],[b[0][bpl:]]+b[1:];assert len(bp)==bpl and len(w)==len(o) and k>0
    aa=em.pre(ap,at);bb=[bp,o]+bt;z1=(q,aa,bb) if side==0 else (q,bb,aa)
    lp,rp=(ap,bp) if side==0 else (bp,ap);L,R=(at,bt) if side==0 else (bt,at);l0,r0,I,O=map(em.lit,(lp,rp,w,o))
    if side==0:src=f'⟨{q}, {l0} ++ {I} ++ L, {r0} ++ R⟩';dst=f'⟨{q}, {l0} ++ L, {r0} ++ {O} ++ R⟩';fn='sweepL'
    else:src=f'⟨{q}, {l0} ++ L, {r0} ++ {I} ++ R⟩';dst=f'⟨{q}, {l0} ++ {O} ++ L, {r0} ++ R⟩';fn='sweepR'
    c1+=k;cost.append(f'{k}*n');out.append(f'theorem one{j} (L R : List Bool) : run0 table {k} {src} = some {dst} := by rfl')
    out.append(f'theorem h{j} (n : Nat) : run0 table ({k}*n) {em.ze(z)} = some {em.ze(z1)} := by\n  simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using ({fn} table {q} {l0} {r0} {I} {O} {k} one{j} n ({em.expr(L)}) ({em.expr(R)}))')
   z=z1
  assert z[0]==goal[0];goalexpr=em.ze(goal);hs=[]
  out.append(f'theorem endEq (n : Nat) : ({em.ze(z)} : Z0) = {goalexpr} := by')
  for j,(a,b) in enumerate(zip(z[1:],goal[1:])):
   if a==b:continue
   hn='hl' if j==0 else 'hr';hs.append(hn);out.append(f'  have {hn} : {em.expr(a)} = {em.expr(b)} := by')
   trs=em.equal_transforms(a,b)
   if not trs:out.append('    rfl');continue
   names=[]
   for ti,(old,new,k,d,w,v,rev) in enumerate(trs):
    name=f'{hn}{ti}';names.append(name);out.append(f'    have {name} : {em.expr(old)} = {em.expr(new)} := by');a,b=old,new
    if rev:a,b=new,old;out.append('      symm')
    prefix=em.expr(a[:k]+[b[k]]);suffix=em.expr(a[k+2:]);out.append(f'      simpa only [List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using (commute_context ({prefix}) ({suffix}) {em.lit(d)} {em.lit(w)} {em.lit(v)} (by decide) n)')
   out.append('    exact '+names[0]+''.join(f'.trans {name}' for name in names[1:]))
  out.append('  rw ['+','.join(hs)+']' if hs else '  rfl')
  target=f'phase{i+1} n' if i<19 else 'phase0 (n+16)'
  out.append(f'theorem goalEq (n : Nat) : ({goalexpr} : Z0) = {target} := by')
  if i<19:out.append('  rfl')
  else:out.append('  unfold phase0\n  rw [show n+16=16+n by omega,rep_add]\n  simp only [List.append_assoc,List.cons_append,List.nil_append]\n  rfl')
  c=f'{c1}*n+{c0}';costs.append(c)
  out.append(f'theorem advance (n : Nat) : run0 table ({c}) (phase{i} n) = some ({target}) := by\n  have h := h0 n')
  for j in range(1,len(actions)):out.append(f'  have h := join0 h (h{j} n)')
  out.append(f'  rw [endEq,goalEq] at h\n  change run0 table _ (phase{i} n) = _ at h\n  rw [show {c} = '+ ' + '.join(cost)+' by omega]\n  exact h\nend Phase'+str(i))
 out.append('inductive inv : Z0 → Prop where')
 for i in range(20):out.append(f'  | p{i} (n : Nat) : inv (phase{i} n)')
 entry=2811;n0=12
 out.append(f'theorem entry : run0 table {entry} ⟨0,[],[]⟩ = some (phase0 {n0}) := by rfl')
 out.append('theorem next (z : Z0) (hz : inv z) : ∃ k z\', 0<k ∧ run0 table k z = some z\' ∧ inv z\' := by\n  cases hz with')
 for i,c in enumerate(costs):
  j=(i+1)%20;n='n' if i<19 else '(n+16)';out.append(f'  | p{i} n => exact ⟨{c},phase{j} {n},by omega,Phase{i}.advance n,inv.p{j} {n}⟩')
 out.append(f'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=\n  never_of_invariant table inv {entry} (phase0 {n0}) entry (inv.p0 {n0}) next m hm\n#print axioms never\nend {NS}')
 Path(outpath).write_text('\n'.join(out)+'\n')
if __name__=='__main__':generate(sys.argv[1])
