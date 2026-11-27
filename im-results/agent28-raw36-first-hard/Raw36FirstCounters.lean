import Raw36FirstRoot
import Raw36FirstDescentA
import Raw36FirstDescentB
import Raw36FirstDescentB1
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6Coverage.Agent31Pump.Auto.Raw36FirstCounters
open BB6Coverage Agent31Pump Auto

def pair : List Bool := [false,true]
def quad : List Bool := [false,true,false,true]
def mark : List Bool := [false,true,true,true]
def suffix : List Bool := [false,false]

/-- Head scans the leftmost zero at the frontier in state A. The parameter
    u>=1 includes the first 01 pair within the fixed head prefix. -/
def A (u v : Nat) : Z0 :=
  ⟨0,[],[false,true,true,true,false,true] ++ rep pair (u-1) ++
      mark ++ rep pair v ++ suffix⟩

/-- Corresponding state B left frontier, again with u>=1. -/
def B (u v : Nat) : Z0 :=
  ⟨1,[],[true] ++ rep pair (u-1) ++ mark ++ rep pair v ++ suffix⟩

theorem rep_add (P : List Bool) (m n : Nat) :
    rep P (m+n) = rep P m ++ rep P n := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simpa only [Nat.succ_add,rep,List.append_assoc] using
      congrArg (fun xs : List Bool => P ++ xs) ih

theorem rep_two (n : Nat) :
    rep pair (2*n) = rep quad n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : 2*(n+1)=2+2*n := by omega
    rw [hn,rep_add]
    change quad ++ rep pair (2*n) = quad ++ rep quad n
    rw [ih]

theorem rep_offset (n k : Nat) :
    rep pair (2*n+k) = rep pair k ++ rep quad n := by
  rw [Nat.add_comm (2*n) k,rep_add,rep_two]

theorem root_a :
    run0 Raw36FirstOverflowA2.p 13244 ⟨0,[],[]⟩ = some (A 17 52) := by
  simpa only [show Raw36FirstRoot.rootA.eval 0 = A 17 52 by decide] using
    Raw36FirstRoot.root13244

theorem root_b :
    run0 Raw36FirstOverflowA2.p 416 ⟨0,[],[]⟩ = some (B 9 1) := by
  simpa only [show Raw36FirstRoot.rootB.eval 0 = B 9 1 by decide] using
    Raw36FirstRoot.root416

#print axioms root_a
#print axioms rep_offset
end BB6Coverage.Agent31Pump.Auto.Raw36FirstCounters
