"""Proof of the nested counter for raw112 hard leaf 77."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent
sys.path[:0]=[str(ROOT.parent/'agent47-raw115-cut'),str(ROOT.parent)]
import counter as c
R,W,C=c.R,c.W,c.C
def literal(s):
    if s.endswith(('X','Y')):return c.app(c.bits(s[:-1]),s[-1])
    return c.bits(s)
c.literal=literal
def generate(p):
    src=c.macro(p,'transferCore',C(5,W('01111',R('11'),'0X'),W('Y')),C(5,W('011',R('11'),'01X'),W('1Y')),True,(9,4))
    src=src.replace('(X : List Bool)','(X Y : List Bool)').replace(' n X)', ' n X Y)').replace(' n X]', ' n X Y]')
    reset=c.macro(p,'resetCore',C(5,W('01101',R('1')),W(R('1'))),C(5,W('01111',R('1'),R('1'),'01'),W()),False,(17,3))
    return '\n\n'.join(['''import Raw115CounterBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6Coverage.Agent31Pump.Raw112Counter77
open BB6Coverage BB6Coverage.Agent31Pump.Raw115CounterBase''',c.pump.tab(p),src,reset,'''abbrev P (n : Nat) := rep [true,true] n
abbrev Q (n : Nat) := rep [true] n

def F (a b : Nat) : Z0 := ⟨5,[false,true,true] ++ P a ++ [false,true] ++ Q b,Q b⟩

theorem transfer (a b : Nat) : run0 table (9+4*a) (F (a+1) b) = some (F a (b+1)) := by
  simpa only [F,P,Q,rep,List.append_assoc,List.cons_append,List.nil_append] using transferCore a ([true] ++ Q b) (Q b)

theorem drain (a b : Nat) : ∃ t, run0 table t (F a b) = some (F 0 (b+a)) := by
  induction a generalizing b with
  | zero => exact ⟨0,by simp [run0]⟩
  | succ a ih =>
    obtain ⟨t,h⟩ := ih (b+1)
    exact ⟨9+4*a+t,by simpa only [Nat.add_assoc,Nat.add_comm 1 a] using join0 (transfer a b) h⟩

theorem reset (n : Nat) : run0 table (17+3*n) (F 0 n) = some (F (n+1) 0) := by
  have h := resetCore n
  have hq := rep_add [true] n n
  have hp := rep_group [true] 2 n
  change rep [true,true] n = rep [true] (2*n) at hp
  rw [show 2*n=n+n by omega,hq] at hp
  simpa only [F,P,Q,rep,hp,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using h

def fam (n : Nat) : Z0 := F n 0

theorem entry : run0 table 10 ⟨0,[],[]⟩ = some (fam 0) := by rfl

theorem growth (n : Nat) : ∃ t, 0<t ∧ run0 table t (fam n) = some (fam (n+1)) := by
  obtain ⟨t,h⟩ := drain n 0
  exact ⟨t+(17+3*n),by omega,by simpa only [fam,Nat.zero_add] using join0 (by simpa only [Nat.zero_add] using h) (reset n)⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_returns table fam (fun _ => True) 0 trivial 10 entry
    (fun n _ => by obtain ⟨t,ht,h⟩ := growth n; exact ⟨n+1,t,trivial,ht,h⟩) m hm
#print axioms never
end BB6Coverage.Agent31Pump.Raw112Counter77'''])+'\n'
if __name__=='__main__':
    rows=(ROOT/'hard.txt').read_text().splitlines()
    (ROOT/'Raw112Counter77.lean').write_text(generate(c.pump.parse(rows[77])))
