import BB429SourceE1Return
import BB429FinishScanEDelta
import Lean.Elab.Tactic.Omega

namespace BB429CZeroToJunc0
open BB429OddExcursion BB429SourceE1Return BB429FinishScanEDelta

/-- A C/0 instruction with the exact contiguous marked/blank left context
    enters the uniform E/1 one-sweep after six literal machine steps. -/
theorem C0_to_E1_6 (n : Nat) :
    run 6 (z 2 (true::false::ones n) false []) =
      some (z 4 (ones n) true [true,false,true]) := by rfl

/-- A complete E/1 left sweep, preserving every cell of arbitrary suffix. -/
theorem E1_ones_sweep (n : Nat) (suffix : List Bool) :
    run n (z 4 (ones n) true suffix) =
      some (z 4 [] true (ones n ++ suffix)) := by
  induction n generalizing suffix with
  | zero => rfl
  | succ n ih =>
      have hfirst : run 1 (z 4 (ones (n+1)) true suffix) =
          some (z 4 (ones n) true (true::suffix)) := by rfl
      have hwords : ones n ++ (true::suffix) = ones (n+1) ++ suffix := by
        simp [ones, List.replicate_succ', List.append_assoc]
      rw [show n+1 = 1+n by omega, run_add, hfirst]
      simp only [Option.bind_some]
      rw [ih (true::suffix), hwords]

/-- Exact parameter-uniform last twelve original actions after this sweep,
    which rebuild a canonical Junc boundary without inspecting its suffix. -/
theorem E1_to_junc12 (suffix : List Bool) :
    run 12 (z 4 [] true (ones 4 ++ suffix)) =
      some (z 0 (ones 6) true suffix) := by rfl

/-- From a fresh C/0 with a 10 alternating prefix and 2k+4 consecutive
    left marks, the next canonical Junc(0,0,2k) is reached after exactly
    2k+22 raw steps, with equality of the ENTIRE infinite zipper tape. -/
theorem C0_to_junc0 (k : Nat) :
    run (2*k+22) (z 2 (true::false::ones (2*k+4)) false []) =
      some (junc 0 0 (2*k)) := by
  have hfirst := C0_to_E1_6 (2*k+4)
  have hsweep := E1_ones_sweep (2*k+4) [true,false,true]
  have htail := E1_to_junc12 (ones (2*k) ++ [true,false,true])
  have hwords : ones (2*k+4) ++ [true,false,true] =
      ones 4 ++ (ones (2*k) ++ [true,false,true]) := by
    rw [show 2*k+4 = 4+2*k by omega, ones_add, List.append_assoc]
  have ht : 2*k+22 = 6+((2*k+4)+12) := by omega
  rw [ht, run_add, hfirst]
  simp only [Option.bind_some]
  rw [run_add, hsweep]
  simp only [Option.bind_some]
  rw [hwords, htail]
  change z 0 (ones 6) true (ones (2*k) ++ [true,false,true]) =
    z 0 (true :: (pairs01 0 ++ ones 5)) true
      (true :: (pairs01 0 ++ ones (2*k) ++ [false,true]))
  rw [show ones 6 = true :: ones 5 by rfl]
  have hr (n : Nat) : ones n ++ [true,false,true] =
      true :: (ones n ++ [false,true]) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        change true :: (ones n ++ [true,false,true]) =
          true :: true :: (ones n ++ [false,true])
        rw [ih]
  rw [hr (2*k)]
  rfl

#print axioms C0_to_E1_6
#print axioms E1_ones_sweep
#print axioms E1_to_junc12
#print axioms C0_to_junc0
end BB429CZeroToJunc0
