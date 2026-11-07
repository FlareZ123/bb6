import BB429E1ShiftDelta
import BB429PhysicalBridge
import Lean.Elab.Tactic.Omega

namespace BB429E1ShiftPhysical
open BB6Coverage
open BB429OddExcursion BB429SourceE1Return BB429E1ShiftDelta BB429PhysicalBridge

private def eState : Fin 6 := ⟨4, by decide⟩
private def e1Move : BB6Coverage.Move := ⟨true, false, eState⟩

/-- A represented E/1 configuration with a nonempty left block takes one
    authentic raw-table step left, preserving the complete tape relation. -/
theorem physical_E1_step (n : Nat) (tail suffix : List Bool)
    (c : Config)
    (hrep : Represents
      (z 4 (true :: (ones n ++ tail)) true (ones 6 ++ suffix)) c) :
    ∃ c', rawStep target429 c = some c' ∧
      Represents (z 4 (ones n ++ tail) true (ones 7 ++ suffix)) c' ∧
      c'.head = c.head - 1 := by
  rcases hrep with ⟨hs, hcur, hleft, hright⟩
  have hstate : c.state = eState := Fin.ext hs
  have hslot : readSlot c = (eState, true) := Prod.ext hstate hcur
  have hrow : target429 (eState, true) = some e1Move := by
    rfl
  have hstep : rawStep target429 c = some (applyMove c e1Move) := by
    simp [rawStep, hslot, hrow, e1Move]
  have hzip :
      zipperLeft
        (z 4 (true :: (ones n ++ tail)) true (ones 6 ++ suffix))
        eState true =
      z 4 (ones n ++ tail) true (ones 7 ++ suffix) := by
    simp [zipperLeft, ones, List.replicate_succ]
  have hrep' := leftRep
    (z 4 (true :: (ones n ++ tail)) true (ones 6 ++ suffix))
    c eState true ⟨hs, hcur, hleft, hright⟩
  refine ⟨applyMove c e1Move, hstep, ?_, ?_⟩
  · simpa [hzip, e1Move] using hrep'
  · simp [applyMove, e1Move]

/-- Raw-physical form of the E/1 left-prefix trace. From any configuration
    representing an E/1 head with n consecutive ones to its left, the first
    j steps (j ≤ n) are exactly j E/1 writes, with head position decreased
    by j and with the complete relative tape represented at every endpoint. -/
theorem physical_left_prefix (n j : Nat) (tail suffix : List Bool)
    (c : Config)
    (hrep : Represents
      (z 4 (ones n ++ tail) true (ones 6 ++ suffix)) c) :
    j ≤ n →
    ∃ c', BB6Coverage.run target429 j c = some c' ∧
      Represents
        (z 4 (ones (n-j) ++ tail) true (ones (j+6) ++ suffix)) c' ∧
      c'.head = c.head - (j : Int) := by
  intro hj
  induction j generalizing n tail suffix c hrep with
  | zero =>
      refine ⟨c, rfl, hrep, ?_⟩
      simp
  | succ j ih =>
      have hn : 0 < n := by omega
      have hrepList : ones n = true :: ones (n-1) := by
        cases n with
        | zero => omega
        | succ n =>
          simp only [ones, Nat.succ_sub_one]
          rw [List.replicate_succ]
      have hstart : Represents
          (z 4 (true :: (ones (n-1) ++ tail)) true (ones 6 ++ suffix)) c := by
        simpa [hrepList] using hrep
      obtain ⟨c1, hstep1, hrep1, hhead1⟩ :=
        physical_E1_step (n-1) tail suffix c hstart
      have hright : ones 7 ++ suffix = ones 6 ++ (ones 1 ++ suffix) := by
        rw [show 7 = 6+1 by omega, ones_add 6 1]
        simp [List.append_assoc]
      have hrep1' : Represents
          (z 4 (ones (n-1) ++ tail) true (ones 6 ++ (ones 1 ++ suffix))) c1 := by
        simpa [hright] using hrep1
      obtain ⟨c2, hrun2, hrep2, hhead2⟩ :=
        ih (n-1) tail (ones 1 ++ suffix) c1 hrep1' (by omega)
      have hleft : n-1-j = n-(1+j) := by omega
      have hright' : ones (j+6) ++ (ones 1 ++ suffix) =
          ones (1+j+6) ++ suffix := by
        have heq : 1+j+6 = (j+6)+1 := by omega
        rw [heq, ones_add (j+6) 1]
        simp [List.append_assoc]
      have hrep2' : Represents
          (z 4 (ones (n-(1+j)) ++ tail) true (ones (1+j+6) ++ suffix)) c2 := by
        simpa [hleft, hright'] using hrep2
      refine ⟨c2, ?_, hrep2', ?_⟩
      · rw [BB429PhysicalBridge.physical_run_succ target429 j c, hstep1]
        simpa using hrun2
      · rw [hhead2, hhead1]
        omega

/-- Every nonempty raw-physical prefix of the original-source `shift_E_11`
    helper is strictly left of its initial head coordinate. This proves the
    one-sided condition *within the macro*. It does not assert that the
    unbounded continuation after the macro never returns to a swept cell. -/
theorem physical_shift_E11_prefix (k j : Nat) (tail suffix : List Bool)
    (c : Config)
    (hrep : Represents
      (z 4 (ones (2*k) ++ tail) true (ones 6 ++ suffix)) c)
    (hj : j ≤ 2*k) :
    ∃ c', BB6Coverage.run target429 j c = some c' ∧
      Represents
        (z 4 (ones (2*k-j) ++ tail) true (ones (j+6) ++ suffix)) c' ∧
      c'.head = c.head - (j : Int) := by
  exact physical_left_prefix (2*k) j tail suffix c hrep hj

/-- The complete `shift_E_11` macro has exact raw head displacement
    `-2*k` and ends at the left endpoint in E/1. -/
theorem physical_shift_E11_total (k : Nat) (tail suffix : List Bool)
    (c : Config)
    (hrep : Represents
      (z 4 (ones (2*k) ++ tail) true (ones 6 ++ suffix)) c) :
    ∃ c', BB6Coverage.run target429 (2*k) c = some c' ∧
      Represents (z 4 tail true (ones (2*k+6) ++ suffix)) c' ∧
      c'.head = c.head - ((2*k : Nat) : Int) := by
  have h := physical_left_prefix (2*k) (2*k) tail suffix c hrep (by omega)
  simpa [ones] using h

/-- Every cell in the leading E/1 sweep is retained as a one. In
    particular, the original head cell is still one after any positive
    prefix, while the head is strictly to its left. -/
private theorem ones_append_getD (n : Nat) (suffix : List Bool) (i : Nat)
    (hi : i < n) :
    (ones n ++ suffix).getD i false = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => simp [ones]
      | succ i =>
          have hi' : i < n := by omega
          simpa [ones, List.replicate_succ] using ih i hi'

/-- The first E/1 write in a `shift_E_11` sweep remains present throughout
    the macro. This is a concrete one-sided last-writer candidate: after
    every positive prefix, the head is left of the original cell and that
    cell still contains one. No claim is made about later J-orbit steps. -/
theorem physical_shift_E11_mark_persists (k j : Nat) (tail suffix : List Bool)
    (c : Config)
    (hrep : Represents
      (z 4 (ones (2*k) ++ tail) true (ones 6 ++ suffix)) c)
    (hj : 0 < j) (hbound : j ≤ 2*k) :
    ∃ c', BB6Coverage.run target429 j c = some c' ∧
      c'.head = c.head - (j : Int) ∧ c'.tape c.head = true := by
  obtain ⟨c', hrun, hrep', hhead⟩ :=
    physical_shift_E11_prefix k j tail suffix c hrep hbound
  rcases hrep' with ⟨_, _, _, hright⟩
  have hpos : c'.head + fcast (j-1) = c.head := by
    rw [hhead]
    simp [fcast]
    omega
  have hget : (ones (j+6) ++ suffix).getD (j-1) false = true :=
    ones_append_getD (j+6) suffix (j-1) (by omega)
  have hmark : c'.tape c.head = true := by
    calc
      c'.tape c.head = c'.tape (c'.head + fcast (j-1)) := by rw [hpos]
      _ = (ones (j+6) ++ suffix).getD (j-1) false := hright (j-1)
      _ = true := hget
  exact ⟨c', hrun, hhead, hmark⟩

#print axioms physical_E1_step
#print axioms physical_left_prefix
#print axioms physical_shift_E11_prefix
#print axioms physical_shift_E11_total
#print axioms physical_shift_E11_mark_persists

end BB429E1ShiftPhysical
