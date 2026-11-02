import Lean.Elab.Tactic.Omega
import BlankTripleCheckpoint
import PaddedApplications

set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
namespace CryptidBoundary

/-- A genuine B section with an immediately following 1 joins that 1 into
    the next unary prefix, preserving the otherwise arbitrary finite suffix. -/
theorem full_B_one (k : Nat) (ys : List Bool) :
    run (12*k*k+49*k+40)
      (init (List.replicate (3*k) true ++ false :: true :: ys)) =
    init (List.replicate (8*k+8) true ++ ys) := by
  have h := full_B k (true::ys)
  have hr :
      List.replicate (8*k+9) true ++ (true::ys) =
      List.replicate ((8*k+8)+2) true ++ ys := by
    calc
      _ = (List.replicate (8*k+9) true ++ List.replicate 1 true) ++ ys := by
        simp [List.append_assoc]
      _ = List.replicate (8*k+9+1) true ++ ys := by
        rw [List.replicate_append_replicate]
      _ = _ := by congr 1
  rw [hr] at h
  exact h.trans (finish_packet_init _ _)

/-- First actual B return beyond one quadrillion primitive raw steps. -/
theorem blank7762150835454696 :
    run 7762150835454696 blank =
      init (List.replicate 188617392 true ++
        [false,true,false,true,false,true,false]) := by
  have ht : 7762150835454696 =
    1091552640110031 + (12*23577173*23577173+49*23577173+40) := by decide
  rw [ht, run_add, blank1091552640110031]
  have hp : oppairs 4 ++ [false] =
    false :: true :: ([false,true,false,true,false,true,false] : List Bool) := by decide
  rw [hp]
  simpa only [Nat.reduceMul,Nat.reduceAdd] using
    (full_B_one 23577173 [false,true,false,true,false,true,false])

/-- Second actual B return, crossing 55 quadrillion raw steps. -/
theorem blank55197514669381024 :
    run 55197514669381024 blank =
      init (List.replicate 502979720 true ++
        [false,true,false,true,false]) := by
  have ht : 55197514669381024 =
    7762150835454696 + (12*62872464*62872464+49*62872464+40) := by decide
  rw [ht, run_add, blank7762150835454696]
  simpa only [Nat.reduceMul,Nat.reduceAdd] using
    (full_B_one 62872464 [false,true,false,true,false])

/-- Genuine blank-origin trajectory past 392 quadrillion primitive steps.
    This end state is physical tape equivalence (ObsEq): it avoids silently
    inserting an explicit zero beyond the final (10)^2 suffix. -/
theorem blank392515651843862508 :
    BB6.BoundaryPadding.ObsEq
      (run 392515651843862508 blank)
      (⟨[],false,List.replicate 1341279253 true ++
         (false :: List.replicate 10 true),5⟩ : Cfg) := by
  have ht : 392515651843862508 =
    55197514669381024 +
      (12*167659906*167659906+49*167659906+50+4*2) := by decide
  rw [ht, run_add, blank55197514669381024]
  have hp : ([false,true,false,true,false] : List Bool) =
    false :: pairs 2 := by decide
  rw [hp]
  have he := BB6.BoundaryPadding.full_E_pairs_implicit_blank 167659906 2
  simpa only [Nat.reduceMul, Nat.reduceAdd] using he

#print axioms full_B_one
#print axioms blank7762150835454696
#print axioms blank55197514669381024
#print axioms blank392515651843862508
end CryptidBoundary
