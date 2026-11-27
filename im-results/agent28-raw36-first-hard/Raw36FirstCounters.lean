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
  | zero => simp [rep]
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


/-- Fixed first-counter prefixes for the machine's two phase states. -/
def Apre (c : Nat) : List Bool :=
  [false,true,true,true,false,true] ++ rep pair (c-1)
def Bpre (c : Nat) : List Bool :=
  [true] ++ rep pair (c-1)
def tailWord (v : Nat) : List Bool := mark ++ rep pair v ++ suffix

/-- A-mode phase word, with the repeated exponent separated from a
    positive odd fixed offset c. -/
theorem A_special (n c v : Nat) (hc : 1 ≤ c) :
    A (2*n+c) v =
      ⟨0,[],Apre c ++ rep quad n ++ tailWord v⟩ := by
  have h : 2*n+c-1 = (c-1)+2*n := by omega
  simp [A,Apre,tailWord,h,rep_add,rep_two,List.append_assoc]

theorem B_special (n c v : Nat) (hc : 1 ≤ c) :
    B (2*n+c) v =
      ⟨1,[],Bpre c ++ rep quad n ++ tailWord v⟩ := by
  have h : 2*n+c-1 = (c-1)+2*n := by omega
  simp [B,Bpre,tailWord,h,rep_add,rep_two,List.append_assoc]

theorem A_target (n c v : Nat) :
    A c (2*n+v) =
      ⟨0,[],(Apre c ++ mark ++ rep pair v) ++ rep quad n ++ suffix⟩ := by
  simp [A,Apre,rep_offset,List.append_assoc]

theorem B_target (n c v : Nat) :
    B c (2*n+v) =
      ⟨1,[],(Bpre c ++ mark ++ rep pair v) ++ rep quad n ++ suffix⟩ := by
  simp [B,Bpre,rep_offset,List.append_assoc]

theorem root_a :
    run0 Raw36FirstOverflowA2.p 13244 ⟨0,[],[]⟩ = some (A 17 52) := by
  simpa [Raw36FirstRoot.p,show Raw36FirstRoot.rootA.eval 0 = A 17 52 by decide] using
    Raw36FirstRoot.root13244

theorem root_b :
    run0 Raw36FirstOverflowA2.p 416 ⟨0,[],[]⟩ = some (B 9 1) := by
  simpa [Raw36FirstRoot.p,show Raw36FirstRoot.rootB.eval 0 = B 9 1 by decide] using
    Raw36FirstRoot.root416

#print axioms root_a
#print axioms rep_offset
end BB6Coverage.Agent31Pump.Auto.Raw36FirstCounters
