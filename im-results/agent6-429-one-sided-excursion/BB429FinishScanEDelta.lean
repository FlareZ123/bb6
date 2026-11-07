import BB429DeltaPhysicalBridge
import Lean.Elab.Tactic.Omega

namespace BB429FinishScanEDelta
open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB6Coverage BB429PhysicalBridge

/-- Additivity of the all-ones block. -/
theorem ones_add (m n : Nat) : ones (m+n) = ones m ++ ones n := by
  induction m with
  | zero => simp [ones]
  | succ m ih => simp [ones, Nat.succ_add, List.replicate_succ]

/-- Additivity of the repeated `01` block. -/
theorem pairs01_add (m n : Nat) : pairs01 (m+n) = pairs01 m ++ pairs01 n := by
  induction m with
  | zero => simp [pairs01]
  | succ m ih =>
      simp only [Nat.succ_add, pairs01]
      rw [ih]
      simp [List.cons_append]

theorem pairs01_succ_append (p : Nat) :
    pairs01 p ++ [false,true] = pairs01 (p+1) := by
  induction p with
  | zero => rfl
  | succ p ih =>
      change false :: true :: (pairs01 p ++ [false,true]) = false :: true :: pairs01 (p+1)
      rw [ih]

/-- One A/1, F/1 pair consumes the two nearest left-hand ones, appends `01`
    immediately after the two-cell right prefix, and moves the head left twice. -/
theorem shift_A11_pair_delta (tail suffix : List Bool) :
    runWithDelta 2 (z 0 (true :: true :: true :: tail) true (true :: suffix)) =
      some (z 0 (true :: tail) true (true :: false :: true :: suffix), -2) := by
  rfl

/-- Exact delta for the complete source `shift_A_11 p` helper. -/
theorem shift_A11_delta (p : Nat) (left suffix : List Bool) :
    runWithDelta (2*p) (z 0 (true :: (ones (2*p) ++ left)) true (true :: suffix)) =
      some (z 0 (true :: left) true (true :: (pairs01 p ++ suffix)), -((2*p : Nat) : Int)) := by
  induction p generalizing left suffix with
  | zero => rfl
  | succ p ih =>
      have hrep : ones (2+2*p) = [true,true] ++ ones (2*p) := by
        calc
          ones (2+2*p) = ones (2*(p+1)) := by congr 1; omega
          _ = ones 2 ++ ones (2*p) := by
            rw [show 2*(p+1) = 2+2*p by omega, ones_add 2 (2*p)]
      have hfirst :
          runWithDelta 2 (z 0 (true :: true :: true :: (ones (2*p) ++ left)) true (true :: suffix)) =
            some (z 0 (true :: (ones (2*p) ++ left)) true (true :: false :: true :: suffix), -2) :=
        shift_A11_pair_delta (ones (2*p) ++ left) suffix
      rw [show 2*(p+1) = 2+2*p by omega, hrep]
      simp only [List.cons_append, List.nil_append]
      rw [runWithDelta_add, hfirst]
      simp only [Option.bind_some]
      have hi := ih left (false :: true :: suffix)
      rw [hi]
      simp only [Option.map_some]
      have hright : pairs01 p ++ (false :: true :: suffix) = pairs01 (p+1) ++ suffix := by
        calc
          pairs01 p ++ (false :: true :: suffix) = pairs01 p ++ ([false,true] ++ suffix) := rfl
          _ = (pairs01 p ++ [false,true]) ++ suffix := by rw [← List.append_assoc]
          _ = pairs01 (p+1) ++ suffix := by rw [pairs01_succ_append]
      rw [hright]
      apply congrArg (fun d : Int =>
        some (z 0 (true :: left) true (true :: (pairs01 (p+1) ++ suffix)), d))
      omega

/-- The twelve-step C/1-to-A preparation leaves the head coordinate unchanged. -/
theorem finishC_to_A_delta (left suffix : List Bool) :
    runWithDelta 12 (z 2 left true (ones 6 ++ suffix)) =
      some (z 0 left true (true :: (pairs01 2 ++ (true :: suffix))), 0) := by
  rfl

/-- Zipper encoding of the source `cfg_Junc u v w` configuration. -/
def junc (u v w : Nat) : Zipper :=
  z 0 (true :: (pairs01 u ++ ones 5)) true
    (true :: (pairs01 v ++ ones w ++ [false,true]))

/-- Zipper encoding of the source `finish_C_ScanE` entry configuration. -/
def finishCStart (u p k : Nat) : Zipper :=
  z 2 (true :: (ones (2*p) ++ pairs01 u ++ ones 5)) true
    (ones 6 ++ ones (2*k) ++ [false,true])

/-- Exact source-level head displacement of `finish_C_ScanE`:
    twelve preparation steps have zero net displacement; the subsequent
    `shift_A_11 p` has displacement `-2p`. The endpoint is exactly
    `cfg_Junc u (p+2) (2k+1)` in zipper form. -/
theorem finishC_ScanE_delta (u p k : Nat) :
    runWithDelta (12 + 2*p) (finishCStart u p k) =
      some (junc u (p+2) (2*k+1), -((2*p : Nat) : Int)) := by
  let left : List Bool := pairs01 u ++ ones 5
  let suffix : List Bool := pairs01 2 ++ (true :: (ones (2*k) ++ [false,true]))
  have hfirst : runWithDelta 12 (finishCStart u p k) =
      some (z 0 (true :: (ones (2*p) ++ left)) true (true :: suffix), 0) := by
    simpa [finishCStart, left, suffix, ones, pairs01, List.append_assoc] using
      (finishC_to_A_delta (true :: (ones (2*p) ++ left)) (ones (2*k) ++ [false,true]))
  have hsecond := shift_A11_delta p left suffix
  rw [runWithDelta_add, hfirst]
  simp only [Option.bind_some]
  rw [hsecond]
  simp only [Option.map_some]
  have hpairs : pairs01 p ++ pairs01 2 = pairs01 (p+2) := by
    rw [← pairs01_add p 2]
  have hones : ones (2*k+1) = true :: ones (2*k) := by
    calc
      ones (2*k+1) = ones (1+2*k) := by congr 1; omega
      _ = ones 1 ++ ones (2*k) := ones_add 1 (2*k)
      _ = true :: ones (2*k) := rfl
  have honesTail : true :: (ones (2*k) ++ [false,true]) =
      ones (2*k+1) ++ [false,true] := by
    rw [← List.cons_append, ← hones]
  have hright : pairs01 p ++ (pairs01 2 ++ (true :: (ones (2*k) ++ [false,true]))) =
      pairs01 (p+2) ++ (ones (2*k+1) ++ [false,true]) := by
    rw [← List.append_assoc, hpairs, honesTail]
  simp only [junc]
  rw [hright]
  simp [left, List.append_assoc]

/-- Lift the exact zipper displacement to the physical `target429` interpreter. -/
theorem physical_finishC_ScanE_delta (u p k : Nat) (c : Config)
    (hrep : Represents (finishCStart u p k) c) :
    ∃ c', BB6Coverage.run BB429PhysicalFrontier.target429 (12+2*p) c = some c' ∧
      Represents (junc u (p+2) (2*k+1)) c' ∧
      c'.head = c.head + -((2*p : Nat) : Int) := by
  obtain ⟨c', hrun, hrep', hhead⟩ :=
    BB429DeltaPhysicalBridge.source_runWithDelta_rep
      (12+2*p) (finishCStart u p k) c hrep
      (junc u (p+2) (2*k+1)) (-((2*p : Nat) : Int))
      (finishC_ScanE_delta u p k)
  exact ⟨c', hrun, hrep', hhead⟩

#print axioms shift_A11_pair_delta
#print axioms shift_A11_delta
#print axioms finishC_to_A_delta
#print axioms finishC_ScanE_delta
#print axioms physical_finishC_ScanE_delta

end BB429FinishScanEDelta
