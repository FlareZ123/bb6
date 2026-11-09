import CZeroContext
import BB429DeltaPhysicalBridge
import Lean.Elab.Tactic.Omega

namespace BB429CZeroContextDelta
open BB429OddExcursion BB429SourceE1Delta
open BB429PhysicalBridge BB429DeltaPhysicalBridge BB6Coverage BB429PhysicalFrontier

private def ones (n : Nat) : List Bool := List.replicate n true

/-- Six primitive source moves; their exact net head displacement is -2. -/
private theorem first_delta (n : Nat) (left right : List Bool) :
    runWithDelta 6
      (z 2 (true::false::(ones n ++ (false::false::left))) false (false::right)) =
    some (z 4 (ones n ++ (false::false::left)) true
      ([true,false,true] ++ right), -2) := by rfl

/-- An all-one E/1 sweep moves exactly n cells left, preserving all tails. -/
private theorem sweep_delta (n : Nat) (left right : List Bool) :
    runWithDelta n (z 4 (ones n ++ left) true right) =
    some (z 4 left true (ones n ++ right), -((n:Nat):Int)) := by
  induction n generalizing left right with
  | zero => rfl
  | succ n ih =>
    have hfirst : runWithDelta 1 (z 4 (ones (n+1) ++ left) true right) =
      some (z 4 (ones n ++ left) true (true::right), -1) := by rfl
    rw [show n+1=1+n by omega, runWithDelta_add,
      show 1+n=n+1 by omega, hfirst]
    simp only [Option.bind_some]
    rw [ih]
    simp only [Option.map_some]
    have hr : ones n ++ (true::right) = ones (n+1) ++ right := by
      simp [ones,List.replicate_succ',List.append_assoc]
    rw [hr]
    apply congrArg some
    apply Prod.ext
    · rfl
    · omega

/-- The two separator blanks yield a twelve-step suffix with displacement +4. -/
private theorem tail12_delta (left right : List Bool) :
    runWithDelta 12 (z 4 (false::false::left) true (ones 4 ++ right)) =
    some (z 0 (ones 6 ++ left) true right, 4) := by rfl

/-- Exact primitive cost, complete tape, and signed head displacement from
    an arbitrarily nonblank remote-left and remote-right C/0 context. -/
theorem czero_context_delta (k : Nat) (left right : List Bool) :
    runWithDelta (2*k+22)
      (z 2 (true::false::(ones (2*k+4) ++ (false::false::left)))
         false (false::right)) =
    some (z 0 (ones 6 ++ left) true
      (ones (2*k+1) ++ (false::true::right)),
      -((2*k+2 : Nat) : Int)) := by
  have hfirst := first_delta (2*k+4) left right
  have hsweep := sweep_delta (2*k+4) (false::false::left)
    ([true,false,true] ++ right)
  have htail := tail12_delta left
    (ones (2*k) ++ ([true,false,true] ++ right))
  have htime : 2*k+22 = 6+((2*k+4)+12) := by omega
  rw [htime,runWithDelta_add,hfirst]
  simp only [Option.bind_some]
  rw [runWithDelta_add,hsweep]
  simp only [Option.map_some,Option.bind_some]
  have hw : ones (2*k+4) ++ ([true,false,true] ++ right) =
    ones 4 ++ (ones (2*k) ++ ([true,false,true] ++ right)) := by
    rw [show 2*k+4=4+2*k by omega]
    simp [ones, ← List.replicate_append_replicate, List.append_assoc]
  rw [hw,htail]
  simp only [Option.map_some]
  apply congrArg some
  apply Prod.ext
  · simp [ones, ← List.replicate_append_replicate, List.append_assoc]
  · omega

/-- Original six-state raw-machine lift, including actual head coordinate. -/
theorem czero_context_original_delta (k : Nat) (left right : List Bool)
    (c : Config)
    (hc : Represents
      (z 2 (true::false::(ones (2*k+4) ++ (false::false::left)))
         false (false::right)) c) :
    ∃ c', BB6Coverage.run target429 (2*k+22) c = some c' ∧
      Represents (z 0 (ones 6 ++ left) true
        (ones (2*k+1) ++ (false::true::right))) c' ∧
      c'.head = c.head - ((2*k+2 : Nat) : Int) := by
  obtain ⟨c', hrun, hrep, hhead⟩ :=
    source_runWithDelta_rep (2*k+22)
      (z 2 (true::false::(ones (2*k+4) ++ (false::false::left)))
        false (false::right)) c hc
      (z 0 (ones 6 ++ left) true
        (ones (2*k+1) ++ (false::true::right)))
      (-((2*k+2 : Nat) : Int)) (czero_context_delta k left right)
  exact ⟨c', hrun, hrep, by omega⟩

#print axioms czero_context_delta
#print axioms czero_context_original_delta
end BB429CZeroContextDelta
