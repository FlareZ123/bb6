"""Reproduce eight kernel-checked Raw56 E1=1LB growth proofs.
Run in the extracted frozen pilot source directory (artifact 15229248243).
"""
from pathlib import Path
from multi_sweep import parse, run_symbolic
from emit_multi import emit_lemma, table, conf
import emit_multi
# Empty prefixes in symbolic words must reduce before associativity.
_original_word=emit_multi.word
def word(a):
    s=_original_word(a)
    return s.removeprefix("([] ++ ").removesuffix(")") if s.startswith("([] ++ ") else s
emit_multi.word=word
emit_multi.SIMP="[List.append_nil,List.nil_append,List.append_assoc,List.cons_append]"
def eq_word(a,b):
    if a==b:return 'rfl'
    A,ma=emit_multi.normalize(a); B,mb=emit_multi.normalize(b); assert A==B,(a,b,A,B)
    lines=['by','    calc']
    def proof(p,s,P,v,var,sym):
        q=f'(moveCut [] {word(s)} {emit_multi.bits(P)} {str(bool(v)).lower()} {var})'+('.symm' if sym else '')
        return f'congrArg (fun tail : List Bool => {word(p+["tail"])}) ({q})'
    for p,s,P,v,var,z in ma:
        lines.append(f'      _ = {word(z)} := by\n        simpa only {emit_multi.SIMP} using {proof(p,s,P,v,var,True)}')
    for p,s,P,v,var,z in reversed(mb):
        z1=p+[[var,[v]+P]]+[v]+s
        lines.append(f'      _ = {word(z1)} := by\n        simpa only {emit_multi.SIMP} using {proof(p,s,P,v,var,False)}')
    if len(ma)+len(mb)==1:return 'by\n    '+lines[-1].split('\n        ')[-1]
    return '\n'.join(lines)
emit_multi.eq_word=eq_word

import json
IDS=[588,959,960,4932,31196,31197,35049,35064]
rows={
588:"1RB1RB_1RC0RF_0RD0LA_1LD1LE_---1LB_0RC0RB",
959:"1RB1RF_1RC0RF_0RD0LA_1LD1LE_---1LB_0RC0RB",
960:"1RB1RF_1RC0RF_0RD0LA_1LD1LE_---1LB_0RC0RF",
4932:"1RB0LA_1RC0RF_0RD0RA_1LD1LE_---1LB_0RC0RB",
31196:"1RB1RC_1RC0RF_0RD1RA_1LD1LE_---1LB_0RC0RB",
31197:"1RB1RC_1RC0RF_0RD1RA_1LD1LE_---1LB_0RC0RF",
35049:"1RB0RF_1RC0RF_0RD1RC_1LD1LE_---1LB_0RC0RA",
35064:"1RB---_1RC0RF_0RD1RC_1LD1LE_---1LB_0RC0RB",
}
# The literal tables are the source obligations; no open-list regeneration required.
Z=('n',(0,)*6); I=('m',(1,)*3); J=('n',(1,)*6)
for i in IDS:
    t=rows[i]; tr=parse(t)
    cases=[('advance',(3,[0,0]+[Z]+[1]*3+[I]+[1,1],[]),(3,[0,0]+[0]*6+[Z]+[I]+[1,1],[])),('reset',(3,[0,0]+[Z]+[1,1],[]),(3,[0,0]+[1]*3+[J]+[1]*2,[]))]
    rr=[]
    for name,a,b in cases:
        z=run_symbolic(tr,a,b); assert z,(i,name)
        rr.append(json.loads(json.dumps(dict(name=name,start=a,target=b,ops=z[0],end=z[1]))))
    a,c1=emit_lemma('advance','n m',rr[0]); b,c2=emit_lemma('reset','n',rr[1]); ns=f'BB6.Agent4Raw56RootE11LB.M{i}'
    out=['import SweepPumping','set_option maxRecDepth 100000','set_option maxHeartbeats 0',f'namespace {ns}','open BB6Coverage BB6Coverage.Agent31Pump',table(t),a,b]
    out.append('''def G (n m : Nat) : Z0 := ⟨3,[false,false] ++ (rep [false,false,false,false,false,false] n ++ (rep [true,true,true] m ++ [true,true])),[]⟩
theorem triple_pair (n : Nat) : rep [true,true,true] (2*n) = rep [true,true,true,true,true,true] n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 2*(n+1)=2*n+2 by omega]; simp only [rep,ih]; rfl
''')
    out.append(f'''def next : Nat × Nat → Nat × Nat
  | (n,0) => (0,2*n+1)
  | (n,m+1) => (n+1,m)
def cost : Nat × Nat → Nat
  | (n,0) => {c2}
  | (n,m+1) => {c1}
theorem positive (z : Nat × Nat) : 0 < cost z := by
  rcases z with ⟨n,m⟩; cases m <;> simp only [cost] <;> omega
theorem return_step (z : Nat × Nat) : run0 table (cost z) (G z.1 z.2) = some (G (next z).1 (next z).2) := by
  rcases z with ⟨n,m⟩; cases m with
  | zero =>
    simp only [cost,next,G,rep.eq_1,rep.eq_2,triple_pair,List.nil_append,List.append_nil]
    exact reset n
  | succ m => exact advance n m
def seq : Nat → Nat × Nat
  | 0 => (0,0)
  | n+1 => next (seq n)
theorem never : ∀ m, compatible table m → NeverHalts m := by
  apply never_of_growth table (fun n => G (seq n).1 (seq n).2) 3 (fun n => cost (seq n))
  · rfl
  · intro n; exact positive _
  · intro n; exact return_step _
#print axioms never
end {ns}''')
    Path(f'rootgrowth/E11LBM{i}.lean').write_text('\n'.join(out)+'\n')
