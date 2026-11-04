import Lean.Elab.Tactic.Omega
import E1101010111ThenA

namespace BB6.Agent37EThenAGuarded

open CryptidBoundary
open BB6.Agent26E1101010111
open BB6.Agent26EThenB

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

/-- A consecutive token-code concatenation is an exact word concatenation. -/
theorem code_append (xs zs : List Bool) :
    CryptidA.wordCode (xs ++ zs) =
      CryptidA.wordCode xs ++ CryptidA.wordCode zs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases x <;> simp [CryptidA.wordCode, ih]

/-- Five consecutive ten-tokens consume the full alternating marker. -/
theorem fiveCode : CryptidA.wordCode (List.replicate 5 false) =
    [true,false,true,false,true,false,true,false,true,false] := by rfl

/-- For q=3u+2 the complete suffix becomes a coded A packet followed by
    an explicit zero exactly when the arbitrary continuation begins with 0. -/
theorem guarded_suffix (u : Nat) (ys : List Bool) :
    List.replicate (2*(3*u+2)+6) true ++ tail (false::ys) =
    CryptidA.wordCode
      (List.replicate (2*u+3) true ++ List.replicate 5 false) ++
        (false :: ys) := by
  rw [code_append, BB6.Agent26EThenA.tripleCode, fiveCode]
  have hn : 2*(3*u+2)+6 = (3*(2*u+3))+1 := by omega
  rw [hn, ← List.replicate_append_replicate]
  simp [tail, List.replicate_succ, List.append_assoc]

/-- The corrected E endpoint is a genuine A-coded input when k=3t+2,
    q=3u+2 and the following physical suffix begins in zero. -/
theorem e_to_a_guarded (t u : Nat) (ys : List Bool) :
    (⟨[],false,List.replicate (8*(3*t+2)+5) true ++
      bWord (3*u+2) (false::ys),5⟩ : Cfg) =
    init (List.replicate (3*(8*t+6)+1) true ++
      false :: (CryptidA.wordCode
        (List.replicate (2*u+3) true ++ List.replicate 5 false) ++
        false :: ys)) := by
  rw [bWord_shape, guarded_suffix]
  have hrep : List.replicate (8*(3*t+2)+5) true =
      true :: true :: List.replicate (3*(8*t+6)+1) true := by
    have hn : 8*(3*t+2)+5=2+(3*(8*t+6)+1) := by omega
    rw [hn]
    calc
      _ = List.replicate 2 true ++
            List.replicate (3*(8*t+6)+1) true := by
              rw [List.replicate_append_replicate]
      _ = _ := by rfl
  rw [hrep]
  rfl

/-- All-parameter, all-continuation two-return exact original-machine theorem
    for k=3t+2 and q=3u+2, with a single required right-suffix zero guard.
    This is conditional on a synthetic symbolic input, not on blank reach. -/
theorem e_then_a_guarded (t u : Nat) (ys : List Bool) :
    let ke := 3*t+2
    let qe := 3*u+2
    let ka := 8*t+6
    let ws := List.replicate (2*u+3) true ++ List.replicate 5 false
    let m := 4*ka+3
    let timeE := 12*ke*ke+49*ke+80+4*qe
    let timeA := (12*ka*ka+41*ka+32) +
      (CryptidA.wordCost m ws+(2*(m+CryptidA.wordInc ws)+6))
    run (timeE+timeA)
      (init (List.replicate (3*ke+2) true ++
        false :: (pairs qe ++ wordE (false::ys)))) =
      ⟨[],false,List.replicate (2*(m+CryptidA.wordInc ws)+5) true ++ ys,5⟩ := by
  dsimp
  rw [run_add, full_E_1101010111_pairs (3*t+2) (3*u+2) (false::ys)]
  rw [e_to_a_guarded]
  exact BB6.Agent35.full_A_code (8*t+6)
    (List.replicate (2*u+3) true ++ List.replicate 5 false) ys

#print axioms guarded_suffix
#print axioms e_to_a_guarded
#print axioms e_then_a_guarded

end BB6.Agent37EThenAGuarded
