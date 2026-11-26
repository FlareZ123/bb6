"""Emit Lean proof of the exact compressed trace using checked macro lemmas."""
import json
from solve_c9_pair import W,y
from pathlib import Path
here=Path(__file__).resolve().parent
trace=json.loads((here/'halt_trace.json').read_text())

def rep(b,n,s):
 return s if n==0 else f'(rep {str(b).lower()} {n} {s})'
def alt(n,s):return s if n==0 else f'(alt {n} {s})'
def wexp(ws):
 if not ws:return 'zero'
 (k,s),*tail=ws
 return alt(k,rep(True,s,'zero' if not tail else f'(push false {wexp(tail)})'))
def rexp(rs):
 b,*tail=rs
 return rep(True,b,'zero' if not tail else rep(False,tail[0],rexp(tail[1:])))
def cutgap(rs):
 if len(rs)==1:return [0]
 g=rs[1];assert g>=2
 return rs[2:] if g==2 else [0,g-2,*rs[2:]]
def pop(w):return w.pop() if w else 0

def inst(e):
 a=e['a'];w=W();w.d.extend(map(tuple,e['W']));r=e['R'];b=r[0];g=r[1] if len(r)>1 else 0;k=b//2
 if e['halt']:
  assert b%2==1 and g==1
  z=[r[2]-1,*r[3:]]
  return 'y_halt_live',f'{a} {k} {wexp(list(w.d))} {rexp(z)}'
 if e['returns']>1:
  n=e['returns']//2;assert n==w.prefix()//3 and e['f']==n
  p,s=w.d.popleft();w.d.appendleft((p-3*n,s))
  return 'triplets',f'{n} {k} {wexp(list(w.d))}'
 u=pop(w)
 if b%2:
  z=rexp(cutgap(r))
  if not w:return 'y_even_terminal',f'{a} {u} {k} {z}'
  v=w.pop();return 'y_even_internal',f'{a} {u} {k} {v-1} {wexp(list(w.d))} {z}'
 if g!=1:
  z=rexp(cutgap(r))
  return ('y_odd_double_succ',f'{a} {u} {k-1} {wexp(list(w.d))} {z}') if k else ('y_odd_double_zero',f'{a} {u} {wexp(list(w.d))} {z}')
 z=rexp([r[2]-1,*r[3:]])
 if k>=2:return 'y_odd_single_two',f'{a} {u} {k-2} {wexp(list(w.d))} {z}'
 if k==1:return 'y_odd_single_one',f'{a} {u} {wexp(list(w.d))} {z}'
 if not w:return 'y_odd_single_zero_terminal',f'{a} {u} {z}'
 v=w.pop();return 'y_odd_single_zero_internal',f'{a} {u} {v-1} {wexp(list(w.d))} {z}'

lines=['import C9PairReturns','set_option maxRecDepth 10000','set_option maxHeartbeats 1000000','set_option linter.unusedSimpArgs false','namespace C9Pair','', 'def blank : Config := ⟨.A,zero,false,zero⟩', '', 'theorem push_rep (b : Bool) (s : Stream) : push b s = rep b 1 s := (rep_one b s).symm', 'theorem one_zero_alt (s : Stream) : rep true 1 (rep false 1 s) = alt 1 s := by rw [rep_one,rep_one,alt_one]', '']
for e in trace:
 i=e['index'];lines.append(f'def cfg{i:03d} : Config := Y {e["a"]} {wexp(e["W"])} {rexp(e["R"])}')
lines+=['','theorem reach000 (short : Bool) : run short 1 blank = some cfg000 := by','  change run short 1 blank = some (Y 1 zero zero)','  simp only [blank,Y,B0,push_zero_blank,rep_one]','  rfl','']
simps='push_rep,one_zero_alt,rep_append,alt_append,rep_zero,alt_zero,rep_zero_blank,push_zero_blank,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,extra,Bool.false_eq_true,ite_false,ite_true'
T=1;F=0
for e in trace:
 i=e['index'];lemma,args=inst(e);n=e['steps'];f=e['f'];s=lambda n,f:f'({n}+extra short*{f})'
 if e['halt']:
  lines += [f'theorem final_local (short : Bool) : ∃ c, run short {n-1} cfg{i:03d} = some c ∧ step short c = none := by',f'  have h := {lemma} short {args}',f'  simpa only [cfg{i:03d},{simps}] using h','',f'theorem exact_halt (short : Bool) : ∃ c, run short {s(T+n-1,F)} blank = some c ∧ step short c = none := by',f'  obtain ⟨c,h,hs⟩ := final_local short',f'  have hr := join (reach{i:03d} short) h','  exact ⟨c,by cases short <;> exact hr,hs⟩','',f'theorem short_halt : ∃ c, run true {T+n-1} blank = some c ∧ step true c = none := exact_halt true',f'theorem long_halt : ∃ c, run false {T+n-1+2*F} blank = some c ∧ step false c = none := exact_halt false','','#print axioms short_halt','#print axioms long_halt','end C9Pair']
  break
 lines += [f'theorem local{i:03d} (short : Bool) : run short {s(n,f)} cfg{i:03d} = some cfg{i+1:03d} := by',f'  have h := {lemma} short {args}',f'  cases short <;> simpa only [cfg{i:03d},cfg{i+1:03d},{simps}] using h','',f'theorem reach{i+1:03d} (short : Bool) : run short {s(T+n,F+f)} blank = some cfg{i+1:03d} := by',f'  have h := join (reach{i:03d} short) (local{i:03d} short)','  cases short <;> exact h','']
 T+=n;F+=f
(here/'C9PairTrace.lean').write_text('\n'.join(lines)+'\n')
print('wrote',len(lines),'lines',T,F)
