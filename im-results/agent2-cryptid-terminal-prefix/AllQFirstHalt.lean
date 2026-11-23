import AllQSourceFeeder
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 4096

namespace BB6.Agent2AllQE1101101100
open CryptidBoundary

def startE (q : Nat) (L ys : List Bool) : Cfg :=
  ⟨[false,false,true] ++ L,false,pairR q ++ word ++ ys,4⟩

def inputI (k q : Nat) (ys : List Bool) : Cfg :=
  init (List.replicate (3*k+2) true ++
        false :: (pairR q ++ word ++ ys))

/- The exact last live configuration, one transition before frozen halt,
   is F reading 1. This is valid for every q, with no scanner cutoff. -/
theorem all_q_e_before_halt (q : Nat) (L ys : List Bool) :
    (run (72+2*q) (startE q L ys)).st = 5 ∧
    (run (72+2*q) (startE q L ys)).h = true := by
  have ht : 72+2*q = 4+(2*q+(3+65)) := by omega
  change (run (72+2*q)
    (⟨[false,false,true] ++ L,false,pairR q ++ word ++ ys,4⟩ : Cfg)).st = 5 ∧
    (run (72+2*q)
    (⟨[false,false,true] ++ L,false,pairR q ++ word ++ ys,4⟩ : Cfg)).h = true
  rw [ht,run_add,prelude4,run_add]
  simp only [List.append_assoc]
  rw [scan_all,run_add,trigger3]
  exact BB6.CryptidEHalt.e_before_halt _ _

theorem frozen_step (c : Cfg) (hc : c.st = 6) : step c = c := by
  rcases c with ⟨l,b,r,st⟩
  change st=6 at hc
  subst st
  cases b <;> rfl

theorem frozen_run (c : Cfg) (hc : c.st = 6) (n : Nat) :
    run n c = c := by
  have hs := frozen_step c hc
  induction n with
  | zero => rfl
  | succ n ih => simpa [run,hs] using ih

/- Frozen halting is reached at the exact first time 73 + 2q;
   no earlier time can be frozen. -/
theorem all_q_e_first_halt (q : Nat) (L ys : List Bool) (t : Nat)
    (ht : t < 73+2*q) :
    (run t (startE q L ys)).st ≠ 6 := by
  intro hc
  have hn : 72+2*q = t+(72+2*q-t) := by omega
  have hh : (run (72+2*q) (startE q L ys)).st = 6 := by
    rw [hn,run_add]
    rw [frozen_run _ hc]
    exact hc
  have hb := (all_q_e_before_halt q L ys).1
  omega

/- Original F/0 input (before taking the unbounded E prefix macro)
   is F-on-1 at the exact primitive step preceding frozen halting. -/
theorem full_E_all_q_before_halt (k q : Nat) (ys : List Bool) :
    (run (12*k*k+41*k+105+2*q) (inputI k q ys)).st = 5 ∧
    (run (12*k*k+41*k+105+2*q) (inputI k q ys)).h = true := by
  have ht : 12*k*k+41*k+105+2*q =
      (12*k*k+41*k+33)+(72+2*q) := by omega
  change (run (12*k*k+41*k+105+2*q)
    (init (List.replicate (3*k+2) true ++
        false :: (pairR q ++ word ++ ys)))).st = 5 ∧
    (run (12*k*k+41*k+105+2*q)
    (init (List.replicate (3*k+2) true ++
        false :: (pairR q ++ word ++ ys)))).h = true
  rw [ht,run_add,prefix_E]
  have hp : pairs (4*k+3) =
      true :: false :: pairs (4*k+2) := by
    rw [show 4*k+3 = (4*k+2)+1 by omega]
    rfl
  rw [hp]
  change (run (72+2*q)
    (startE q (false :: pairs (4*k+2) ++ [true,true]) ys)).st = 5 ∧
    (run (72+2*q)
    (startE q (false :: pairs (4*k+2) ++ [true,true]) ys)).h = true
  exact all_q_e_before_halt q _ ys

/- Precise first frozen halt for the original F-on-zero input family. -/
theorem full_E_all_q_exact_first_halt (k q : Nat) (ys : List Bool)
    (t : Nat) (ht : t < 12*k*k+41*k+106+2*q) :
    (run t (inputI k q ys)).st ≠ 6 := by
  intro hc
  have hn : 12*k*k+41*k+105+2*q =
      t+(12*k*k+41*k+105+2*q-t) := by omega
  have hh : (run (12*k*k+41*k+105+2*q) (inputI k q ys)).st = 6 := by
    rw [hn,run_add]
    rw [frozen_run _ hc]
    exact hc
  have hb := (full_E_all_q_before_halt k q ys).1
  omega

#print axioms all_q_e_before_halt
#print axioms all_q_e_first_halt
#print axioms full_E_all_q_before_halt
#print axioms full_E_all_q_exact_first_halt
end BB6.Agent2AllQE1101101100
