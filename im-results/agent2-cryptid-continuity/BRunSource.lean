import Lean.Elab.Tactic.Omega
import Boundary
import BRunValuation

namespace BB6.CryptidBRun
open CryptidBoundary

def I (n : Nat) (ys : List Bool) : Cfg :=
  ⟨[], false, List.replicate n true ++ ys, 5⟩

/-- Direct source-machine realization of any arithmetic BStep, provided the
    current F-section has a zero delimiter and an arbitrary trailing suffix. -/
theorem source_B_step {n m : Nat} (ys : List Bool) (h : BStep n m) :
    ∃ t, run t (I n (false::ys)) = I m ys := by
  obtain ⟨k, hn, hm⟩ := step_index h
  subst n
  subst m
  refine ⟨12*k*k+49*k+40, ?_⟩
  have hr : List.replicate (3*k+2) true =
      [true,true] ++ List.replicate (3*k) true := by
    calc
      List.replicate (3*k+2) true = List.replicate (2+3*k) true := by congr 1; omega
      _ = List.replicate 2 true ++ List.replicate (3*k) true :=
        (List.replicate_append_replicate).symm
      _ = _ := rfl
  simpa only [I, init, hr, List.append_assoc, List.cons_append, List.nil_append] using (full_B k ys)

/-- Every certified arithmetic j-branch B chain executes on the original
    six-state machine when the suffix supplies j explicit zero delimiters. -/
theorem source_B_chain {j n z : Nat} (ys : List Bool)
    (h : BRun j n z) :
    ∃ t, run t (I n (List.replicate j false ++ ys)) = I z ys := by
  induction h generalizing ys with
  | zero n =>
    exact ⟨0, rfl⟩
  | @succ j n m z hs tail ih =>
    obtain ⟨t1, h1⟩ := source_B_step (List.replicate j false ++ ys) hs
    obtain ⟨t2, h2⟩ := ih ys
    refine ⟨t1+t2, ?_⟩
    have ht :
      run (t1+t2) (I n (false :: (List.replicate j false ++ ys))) = I z ys := by
      rw [run_add, h1, h2]
    simpa only [List.replicate, List.cons_append, List.append_assoc] using ht

/-- Exact divisibility suffices for an original-machine finite execution
    through j successive B macros, with j zero delimiters available. -/
theorem source_B_chain_from_dvd (j n : Nat) (ys : List Bool)
    (hd : 3^j ∣ 5*n+11) :
    ∃ z t, run t (I n (List.replicate j false ++ ys)) = I z ys := by
  obtain ⟨z,hz⟩ := three_power_constructs_run j n hd
  obtain ⟨t, ht⟩ := source_B_chain ys hz
  exact ⟨z,t,ht⟩

#print axioms source_B_step
#print axioms source_B_chain
#print axioms source_B_chain_from_dvd
end BB6.CryptidBRun
