import BB429OddExcursion
import BB429PhysicalBridge
import Lean.Elab.Tactic.Omega

namespace BB429CZeroContext
open BB429OddExcursion

private def marked (n : Nat) : List Bool := List.replicate n true

/-- The first six literal instructions leave all remote left/right bits intact. -/
private theorem first (n : Nat) (left right : List Bool) :
    run 6
      (z 2 (true::false::(marked n ++ (false::false::left)))
        false (false::right)) =
    some (z 4 (marked n ++ (false::false::left))
      true ([true,false,true] ++ right)) := by rfl

/-- E/1 scans exactly the indicated marked block, with arbitrary context. -/
private theorem sweep (n : Nat) (left right : List Bool) :
    run n (z 4 (marked n ++ left) true right) =
    some (z 4 left true (marked n ++ right)) := by
  induction n generalizing left right with
  | zero => rfl
  | succ n ih =>
    have hfirst : run 1 (z 4 (marked (n+1) ++ left) true right) =
      some (z 4 (marked n ++ left) true (true::right)) := by rfl
    rw [show n+1=1+n by omega, run_add]
    rw [show 1+n=n+1 by omega, hfirst]
    simp only [Option.bind_some]
    rw [ih]
    congr 1
    simp [marked, List.replicate_succ', List.append_assoc]

/-- The two blank separator cells are consumed by the fixed twelve-step tail. -/
private theorem tail12 (left right : List Bool) :
    run 12 (z 4 (false::false::left) true (marked 4 ++ right)) =
    some (z 0 (marked 6 ++ left) true right) := by rfl

/-- Exact C/0-to-canonical-chart corridor with arbitrary unvisited tape tails.
    Unlike the earlier empty-tail formula, this permits genuinely nonblank
    remote tape. Only the displayed finite pattern and two separator blanks
    are required; the two tails are transported without inspection. -/
theorem czero_context (k : Nat) (left right : List Bool) :
    run (2*k+22)
      (z 2 (true::false::(marked (2*k+4) ++ (false::false::left)))
         false (false::right)) =
    some (z 0 (marked 6 ++ left) true
      (marked (2*k+1) ++ (false::true::right))) := by
  have hfirst := first (2*k+4) left right
  have hsweep := sweep (2*k+4) (false::false::left)
    ([true,false,true] ++ right)
  have htail := tail12 left
    (marked (2*k) ++ ([true,false,true] ++ right))
  have htime : 2*k+22 = 6+((2*k+4)+12) := by omega
  rw [htime,run_add,hfirst]
  simp only [Option.bind_some]
  rw [run_add,hsweep]
  simp only [Option.bind_some]
  have hw : marked (2*k+4) ++ ([true,false,true] ++ right) =
    marked 4 ++ (marked (2*k) ++ ([true,false,true] ++ right)) := by
    rw [show 2*k+4=4+2*k by omega]
    simp [marked, ← List.replicate_append_replicate]
  rw [hw,htail]
  congr 1
  simp [marked, ← List.replicate_append_replicate]

/-- Whole original six-state physical-tape transport of the arbitrary-tail
    theorem. The premise represents the complete tape, not a finite window. -/
theorem czero_context_original (k : Nat) (left right : List Bool)
    (c : BB6Coverage.Config)
    (hc : BB429PhysicalBridge.Represents
      (z 2 (true::false::(marked (2*k+4) ++ (false::false::left)))
         false (false::right)) c) :
    ∃ c', BB6Coverage.run BB429PhysicalFrontier.target429 (2*k+22) c =
      some c' ∧
      BB429PhysicalBridge.Represents
        (z 0 (marked 6 ++ left) true
          (marked (2*k+1) ++ (false::true::right))) c' := by
  exact BB429PhysicalBridge.source_run_rep _ _ _ hc _ (czero_context k left right)

#print axioms czero_context
#print axioms czero_context_original
end BB429CZeroContext
