import BB429FinishScanEDelta
import Lean.Elab.Tactic.Omega

namespace BB429JuncHeadExcursion
open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta BB429FinishScanEDelta BB6Coverage BB429PhysicalBridge

/-- One A/0,B/1 pair shifts 01 from right to left and moves right twice. -/
theorem shift_A01_pair_delta (left suffix : List Bool) :
    runWithDelta 2 (z 0 left false (true :: suffix)) =
      some (z 0 (true :: true :: left) (suffix.headD false) suffix.tail, 2) := by
  cases suffix <;> rfl

/-- Exact delta for shifting n 01 pairs through state A. The final right
    suffix is assumed to begin with the one under the head. -/
theorem shift_A01_delta (v : Nat) (left suffix : List Bool) :
    runWithDelta (2*(v+1))
      (z 0 left false (true :: (pairs01 v ++ (true :: suffix)))) =
      some (z 0 (ones (2*(v+1)) ++ left) true suffix, ((2*(v+1) : Nat) : Int)) := by
  induction v generalizing left suffix with
  | zero =>
      simpa [pairs01, ones] using
        (shift_A01_pair_delta left (true :: suffix))
  | succ v ih =>
      have hpair :
          runWithDelta 2
            (z 0 left false (true :: (pairs01 (v+1) ++ (true :: suffix)))) =
            some (z 0 (true :: true :: left) false
              (true :: (pairs01 v ++ (true :: suffix))), 2) := by
        simpa [pairs01, List.append_assoc] using
          (shift_A01_pair_delta left (false :: true :: (pairs01 v ++ (true :: suffix))))
      rw [show 2*(v+2) = 2 + 2*(v+1) by omega, runWithDelta_add, hpair]
      simp only [Option.bind_some]
      rw [ih (true :: true :: left) suffix]
      simp only [Option.map_some]
      have hones : ones (2+2*(v+1)) = ones (2*(v+1)) ++ [true,true] := by
        rw [show 2+2*(v+1) = 2*(v+1)+2 by omega]
        simpa [ones] using (ones_add (2*(v+1)) 2)
      rw [hones]
      simp [List.append_assoc]

/-- Four-instruction preparation at the front of step_u_pos_to_MidA for
    the u=2 Junc family. -/
theorem junc2_prep4_delta (v w : Nat) :
    runWithDelta 4 (junc 2 v w) =
      some (z 0 (true :: true :: true :: (pairs01 1 ++ ones 5)) false
        (true :: (pairs01 v ++ ones w ++ [false,true])), 0) := by
  rfl

/-- The intermediate A configuration after step_u_pos_to_MidA v when u=2. -/
def midA2 (v w : Nat) : Zipper :=
  z 0 (true :: (ones (2*(v+2)) ++ pairs01 1 ++ ones 5)) true
    (ones (w-1) ++ [false,true])

theorem junc2_to_midA_delta (v w : Nat) (hw : 1 ≤ w) :
    runWithDelta (2*v+6) (junc 2 v w) =
      some (midA2 v w, ((2*v+2 : Nat) : Int)) := by
  have hones : ones w = true :: ones (w-1) := by
    cases w with
    | zero => omega
    | succ w => rfl
  have hprep := junc2_prep4_delta v w
  rw [show 2*v+6 = 4 + 2*(v+1) by omega, runWithDelta_add, hprep]
  simp only [Option.bind_some]
  have hshift :
      runWithDelta (2*(v+1))
        (z 0 (true :: true :: true :: (pairs01 1 ++ ones 5)) false
          (true :: (pairs01 v ++ ones w ++ [false,true]))) =
      some (z 0 (ones (2*(v+1)) ++ true :: true :: true :: (pairs01 1 ++ ones 5)) true
        (ones (w-1) ++ [false,true]), ((2*(v+1) : Nat) : Int)) := by
    simpa [hones, List.append_assoc, List.cons_append] using
      (shift_A01_delta v (true :: true :: true :: (pairs01 1 ++ ones 5))
        (ones (w-1) ++ [false,true]))
  rw [hshift]
  simp only [Option.map_some]
  have hprefix : ones (2*(v+1)) ++ [true,true,true] =
      true :: ones (2*(v+2)) := by
    calc
      ones (2*(v+1)) ++ [true,true,true] =
          ones (2*(v+1)) ++ ones 3 := rfl
      _ = ones (2*(v+1)+3) := by rw [← ones_add]
      _ = ones (1+2*(v+2)) := by congr 1 <;> omega
      _ = ones 1 ++ ones (2*(v+2)) := ones_add 1 _
      _ = true :: ones (2*(v+2)) := rfl
  have hleft :
      ones (2*(v+1)) ++ (true :: true :: true :: (pairs01 1 ++ ones 5)) =
      true :: (ones (2*(v+2)) ++ pairs01 1 ++ ones 5) := by
    calc
      ones (2*(v+1)) ++ (true :: true :: true :: (pairs01 1 ++ ones 5)) =
          (ones (2*(v+1)) ++ [true,true,true]) ++ (pairs01 1 ++ ones 5) := by
            exact (List.append_assoc (ones (2*(v+1))) [true,true,true] (pairs01 1 ++ ones 5)).symm
      _ = (true :: ones (2*(v+2))) ++ (pairs01 1 ++ ones 5) := by rw [hprefix]
      _ = true :: (ones (2*(v+2)) ++ pairs01 1 ++ ones 5) := by
        rw [List.cons_append, List.append_assoc]
  rw [hleft]
  simp [midA2, List.append_assoc, Int.natCast_add, Int.natCast_mul]
  <;> omega

/-- Complete u=2 Junc transition for w>=2. The head first reaches midA2
    at offset 2v+2, then shift_A_11(v+2) returns it to offset -2. -/
theorem junc2_next_delta (v w : Nat) (hw : 2 ≤ w) :
    runWithDelta (4*v+10) (junc 2 v w) =
      some (junc 1 (v+2) (w-2), -2) := by
  have hmid := junc2_to_midA_delta v w (by omega)
  have hones : ones (w-1) = true :: ones (w-2) := by
    cases w with
    | zero => omega
    | succ w => cases w with
      | zero => omega
      | succ w => rfl
  rw [show 4*v+10 = (2*v+6) + 2*(v+2) by omega, runWithDelta_add, hmid]
  simp only [Option.bind_some]
  have hinput : midA2 v w =
      z 0 (true :: (ones (2*(v+2)) ++ (pairs01 1 ++ ones 5))) true
        (true :: (ones (w-2) ++ [false,true])) := by
    simp [midA2, hones, List.append_assoc, List.cons_append]
  have hshift :
      runWithDelta (2*(v+2)) (midA2 v w) =
        some (junc 1 (v+2) (w-2), -((2*(v+2) : Nat) : Int)) := by
    rw [hinput]
    simpa [junc, pairs01, List.append_assoc, List.cons_append] using
      (shift_A11_delta (v+2) (pairs01 1 ++ ones 5) (ones (w-2) ++ [false,true]))
  rw [hshift]
  simp only [Option.map_some]
  simp [Int.natCast_add, Int.natCast_mul]
  omega

/-- Fixed twenty-step prefix of step_u0_to_B; it writes the first three
    01 pairs on the right and moves the head left four cells. -/
theorem junc0_prep20_delta (v w : Nat) :
    runWithDelta 20 (junc 0 v w) =
      some (z 1 (ones 5) false (true :: (pairs01 (v+2) ++ ones w ++ [false,true])), -4) := by
  rfl

/-- One B/0,C/1 pair shifts 01 from right to left and moves right twice. -/
theorem shift_B01_pair_delta (left suffix : List Bool) :
    runWithDelta 2 (z 1 left false (true :: suffix)) =
      some (z 1 (false :: true :: left) (suffix.headD false) suffix.tail, 2) := by
  cases suffix <;> rfl

/-- Exact delta for shifting v+1 01 pairs through state B. -/
theorem shift_B01_delta (v : Nat) (left suffix : List Bool) :
    runWithDelta (2*(v+1))
      (z 1 left false (true :: (pairs01 v ++ (true :: suffix)))) =
      some (z 1 (pairs01 (v+1) ++ left) true suffix, ((2*(v+1) : Nat) : Int)) := by
  induction v generalizing left suffix with
  | zero =>
      simpa [pairs01] using (shift_B01_pair_delta left (true :: suffix))
  | succ v ih =>
      have hpair :
          runWithDelta 2
            (z 1 left false (true :: (pairs01 (v+1) ++ (true :: suffix)))) =
            some (z 1 (false :: true :: left) false
              (true :: (pairs01 v ++ (true :: suffix))), 2) := by
        simpa [pairs01, List.append_assoc] using
          (shift_B01_pair_delta left (false :: true :: (pairs01 v ++ (true :: suffix))))
      rw [show 2*(v+2) = 2 + 2*(v+1) by omega, runWithDelta_add, hpair]
      simp only [Option.bind_some]
      rw [ih (false :: true :: left) suffix]
      simp only [Option.map_some]
      have hleft : pairs01 (v+1) ++ (false :: true :: left) =
          pairs01 (v+2) ++ left := by
        calc
          pairs01 (v+1) ++ (false :: true :: left) =
              pairs01 (v+1) ++ ([false,true] ++ left) := rfl
          _ = (pairs01 (v+1) ++ [false,true]) ++ left := by rw [← List.append_assoc]
          _ = pairs01 (v+2) ++ left := by rw [pairs01_succ_append]
      rw [hleft]
      simp

/-- The full step_u0_to_B v path has head displacement 2v+2. -/
theorem junc0_to_B_delta (v w : Nat) (hw : 1 ≤ w) :
    runWithDelta (2*v+26) (junc 0 v w) =
      some (z 1 (pairs01 (v+3) ++ ones 5) true (ones (w-1) ++ [false,true]), ((2*v+2 : Nat) : Int)) := by
  have hones : ones w = true :: ones (w-1) := by
    cases w with
    | zero => omega
    | succ w => rfl
  rw [show 2*v+26 = 20 + 2*(v+3) by omega, runWithDelta_add, junc0_prep20_delta]
  simp only [Option.bind_some]
  have hshift :
      runWithDelta (2*(v+3))
        (z 1 (ones 5) false (true :: (pairs01 (v+2) ++ ones w ++ [false,true]))) =
      some (z 1 (pairs01 (v+3) ++ ones 5) true (ones (w-1) ++ [false,true]),
        ((2*(v+3) : Nat) : Int)) := by
    have hbase := shift_B01_delta (v+2) (ones 5) (ones (w-1) ++ [false,true])
    have hinput :
        z 1 (ones 5) false (true :: (pairs01 (v+2) ++ ones w ++ [false,true])) =
        z 1 (ones 5) false (true :: (pairs01 (v+2) ++ (true :: (ones (w-1) ++ [false,true])))) := by
      rw [hones]
      congr 1
      rw [List.append_assoc, List.cons_append]
    rw [← hinput] at hbase
    exact hbase
  rw [hshift]
  simp only [Option.map_some]
  simp [Int.natCast_add, Int.natCast_mul]
  omega

/-- For w>=3, the u=0 Junc macro ends at a later head offset 2v+3. -/
theorem junc0_next_delta (v w : Nat) (hw : 3 ≤ w) :
    runWithDelta (2*v+27) (junc 0 v w) =
      some (junc (v+3) 0 (w-3), ((2*v+3 : Nat) : Int)) := by
  have hB := junc0_to_B_delta v w (by omega)
  rw [show 2*v+27 = (2*v+26)+1 by omega, runWithDelta_add, hB]
  simp only [Option.bind_some]
  have hlast : runWithDelta 1
      (z 1 (pairs01 (v+3) ++ ones 5) true (ones (w-1) ++ [false,true])) =
      some (z 0 (true :: (pairs01 (v+3) ++ ones 5)) true
        (ones (w-2) ++ [false,true]), 1) := by
    cases w with
    | zero => omega
    | succ w => cases w with
      | zero => omega
      | succ w => rfl
  have honesTail : ones (w-2) = true :: ones (w-3) := by
    cases w with
    | zero => omega
    | succ w => cases w with
      | zero => omega
      | succ w => cases w with
        | zero => omega
        | succ w => rfl
  have hlast' : runWithDelta 1
      (z 1 (pairs01 (v+3) ++ ones 5) true (ones (w-1) ++ [false,true])) =
      some (junc (v+3) 0 (w-3), 1) := by
    simpa [junc, pairs01, honesTail, List.cons_append, List.append_assoc] using hlast
  rw [hlast']
  simp [Int.natCast_add, Int.natCast_mul]
  omega

/-- Right suffix of the post-shift S_E configurations used in the return chain. -/
def sourceSuffix (k : Nat) : List Bool := ones 6 ++ ones (2*k) ++ [false,true]

/-- The even-b S_E return lands exactly at the C/1 entry of finish_C_ScanE
    with p=b and middle alternating block length two. -/
theorem finalLeft_even_finishC_entry (r k : Nat) :
    z 2 (finalLeft (2*r)) true (sourceSuffix k) = finishCStart 2 (2*r) k := by
  have hhead : ones (4*r+1) = true :: ones (4*r) := by
    calc
      ones (4*r+1) = ones (1+4*r) := by congr 1 <;> omega
      _ = ones 1 ++ ones (4*r) := ones_add 1 _
      _ = true :: ones (4*r) := rfl
  rw [finalLeft_even, hhead, show 4*r = 2*(2*r) by omega]
  simp [finishCStart, sourceSuffix, pairs01, List.append_assoc, List.cons_append]

/-- The odd-b S_E return lands at the C/1 entry with no middle 01 block. -/
theorem finalLeft_odd_finishC_entry (r k : Nat) :
    z 2 (finalLeft (2*r+1)) true (sourceSuffix k) = finishCStart 0 (2*r+1) k := by
  have hleft : ones (4*r+8) = true :: (ones (4*r+2) ++ ones 5) := by
    calc
      ones (4*r+8) = ones (1+(4*r+7)) := by congr 1 <;> omega
      _ = ones 1 ++ ones (4*r+7) := ones_add 1 _
      _ = true :: (ones (4*r+2) ++ ones 5) := by
        rw [show 4*r+7 = (4*r+2)+5 by omega, ones_add]
        rfl
  rw [finalLeft_odd, hleft]
  simp [finishCStart, sourceSuffix, pairs01, List.append_assoc,
    show 2*(2*r+1) = 4*r+2 by omega]

/-- Exact composition from an even-parameter S_E/1 boundary through the
    source E/1 return and finish_C_ScanE to Junc. -/
theorem sourceScanE_finishC_even_delta (r k : Nat) :
    runWithDelta (crossTime (2*r)+1 + (12+2*(2*r)))
      (sourceScanE (2*r) (sourceSuffix k)) =
      some (junc 2 (2*r+2) (2*k+1), -((2*(2*r) : Nat) : Int)) := by
  rw [runWithDelta_add, sourceScanE_e1_revisit_delta]
  simp only [Option.bind_some]
  rw [finalLeft_even_finishC_entry, finishC_ScanE_delta]
  simp

/-- Exact composition from an odd-parameter S_E/1 boundary through the
    source E/1 return and finish_C_ScanE to Junc. -/
theorem sourceScanE_finishC_odd_delta (r k : Nat) :
    runWithDelta (crossTime (2*r+1)+1 + (12+2*(2*r+1)))
      (sourceScanE (2*r+1) (sourceSuffix k)) =
      some (junc 0 (2*r+3) (2*k+1), -((2*(2*r+1) : Nat) : Int)) := by
  rw [runWithDelta_add, sourceScanE_e1_revisit_delta]
  simp only [Option.bind_some]
  rw [finalLeft_odd_finishC_entry, finishC_ScanE_delta]
  simp

/-- For even b, the following Junc-to-MidA excursion reaches a head exactly
    six cells to the right of the post-shift S_E boundary. -/
theorem sourceScanE_finishC_even_midA_delta (r k : Nat) :
    runWithDelta
      ((crossTime (2*r)+1 + (12+2*(2*r))) + (2*(2*r+2)+6))
      (sourceScanE (2*r) (sourceSuffix k)) =
      some (midA2 (2*r+2) (2*k+1), 6) := by
  rw [runWithDelta_add, sourceScanE_finishC_even_delta]
  simp only [Option.bind_some]
  rw [junc2_to_midA_delta (2*r+2) (2*k+1) (by omega)]
  simp only [Option.map_some]
  simp [Int.natCast_add, Int.natCast_mul]
  omega

/-- For odd b and k>=1, the following Junc macro reaches a head exactly
    seven cells to the right of the post-shift S_E boundary. -/
theorem sourceScanE_finishC_odd_next_delta (r k : Nat) (hk : 1 ≤ k) :
    runWithDelta
      ((crossTime (2*r+1)+1 + (12+2*(2*r+1))) + (2*(2*r+3)+27))
      (sourceScanE (2*r+1) (sourceSuffix k)) =
      some (junc (2*r+6) 0 ((2*k+1)-3), 7) := by
  rw [runWithDelta_add, sourceScanE_finishC_odd_delta]
  simp only [Option.bind_some]
  rw [junc0_next_delta (2*r+3) (2*k+1) (by omega)]
  simp only [Option.map_some]
  simp [Int.natCast_add, Int.natCast_mul]
  omega

/-- Physical lift of the even-b six-cell rightward excursion. -/
theorem physical_sourceScanE_finishC_even_midA_delta (r k : Nat) (c : Config)
    (hrep : Represents (sourceScanE (2*r) (sourceSuffix k)) c) :
    ∃ c', BB6Coverage.run target429
      ((crossTime (2*r)+1 + (12+2*(2*r))) + (2*(2*r+2)+6)) c = some c' ∧
      Represents (midA2 (2*r+2) (2*k+1)) c' ∧ c'.head = c.head + 6 := by
  obtain ⟨c', hrun, hrep', hhead⟩ :=
    BB429DeltaPhysicalBridge.source_runWithDelta_rep
      ((crossTime (2*r)+1 + (12+2*(2*r))) + (2*(2*r+2)+6))
      (sourceScanE (2*r) (sourceSuffix k)) c hrep
      (midA2 (2*r+2) (2*k+1)) 6
      (sourceScanE_finishC_even_midA_delta r k)
  exact ⟨c', hrun, hrep', hhead⟩

/-- Physical lift of the odd-b seven-cell rightward excursion. -/
theorem physical_sourceScanE_finishC_odd_next_delta (r k : Nat) (hk : 1 ≤ k)
    (c : Config) (hrep : Represents (sourceScanE (2*r+1) (sourceSuffix k)) c) :
    ∃ c', BB6Coverage.run target429
      ((crossTime (2*r+1)+1 + (12+2*(2*r+1))) + (2*(2*r+3)+27)) c = some c' ∧
      Represents (junc (2*r+6) 0 ((2*k+1)-3)) c' ∧ c'.head = c.head + 7 := by
  obtain ⟨c', hrun, hrep', hhead⟩ :=
    BB429DeltaPhysicalBridge.source_runWithDelta_rep
      ((crossTime (2*r+1)+1 + (12+2*(2*r+1))) + (2*(2*r+3)+27))
      (sourceScanE (2*r+1) (sourceSuffix k)) c hrep
      (junc (2*r+6) 0 ((2*k+1)-3)) 7
      (sourceScanE_finishC_odd_next_delta r k hk)
  exact ⟨c', hrun, hrep', hhead⟩

def midApos (u v w : Nat) : Zipper :=
  z 0 (true :: (ones (2*(v+2)) ++ pairs01 u ++ ones 5)) true
    (ones (w-1) ++ [false,true])

/-- Three newly written ones absorb the fixed 01 prefix after the A/01 sweep. -/
theorem ones_three_left (n : Nat) (rest : List Bool) :
    ones n ++ (true :: true :: true :: rest) =
      true :: (ones (n+2) ++ rest) := by
  have hp : ones n ++ [true,true,true] = true :: ones (n+2) := by
    calc
      ones n ++ [true,true,true] = ones n ++ ones 3 := rfl
      _ = ones (n+3) := by rw [← ones_add]
      _ = ones (1+(n+2)) := by congr 1 <;> omega
      _ = ones 1 ++ ones (n+2) := ones_add 1 _
      _ = true :: ones (n+2) := rfl
  calc
    ones n ++ (true :: true :: true :: rest) =
        (ones n ++ [true,true,true]) ++ rest := by
          exact (List.append_assoc (ones n) [true,true,true] rest).symm
    _ = (true :: ones (n+2)) ++ rest := by rw [hp]
    _ = true :: (ones (n+2) ++ rest) := by rw [List.cons_append]

/-- The fixed four-step prefix of step_u_pos_to_MidA works for every
    positive Junc left parameter. -/
theorem juncPos_prep4_delta (u v w : Nat) :
    runWithDelta 4 (junc (u+1) v w) =
      some (z 0 (true :: true :: true :: (pairs01 u ++ ones 5)) false
        (true :: (pairs01 v ++ ones w ++ [false,true])), 0) := by
  rfl

/-- General positive-u Junc-to-MidA displacement. -/
theorem juncPos_to_midA_delta (u v w : Nat) (hw : 1 ≤ w) :
    runWithDelta (2*v+6) (junc (u+1) v w) =
      some (midApos u v w, ((2*v+2 : Nat) : Int)) := by
  have hones : ones w = true :: ones (w-1) := by
    cases w with
    | zero => omega
    | succ w => rfl
  rw [show 2*v+6 = 4 + 2*(v+1) by omega, runWithDelta_add,
    juncPos_prep4_delta]
  simp only [Option.bind_some]
  have hshift :
      runWithDelta (2*(v+1))
        (z 0 (true :: true :: true :: (pairs01 u ++ ones 5)) false
          (true :: (pairs01 v ++ ones w ++ [false,true]))) =
      some (z 0 (ones (2*(v+1)) ++ true :: true :: true :: (pairs01 u ++ ones 5)) true
        (ones (w-1) ++ [false,true]), ((2*(v+1) : Nat) : Int)) := by
    simpa [hones, List.append_assoc, List.cons_append] using
      (shift_A01_delta v (true :: true :: true :: (pairs01 u ++ ones 5))
        (ones (w-1) ++ [false,true]))
  rw [hshift]
  simp only [Option.map_some]
  rw [ones_three_left (2*(v+1)) (pairs01 u ++ ones 5)]
  apply congrArg some
  apply Prod.ext
  · simp only [midApos]
    rw [show 2*(v+1)+2 = 2*(v+2) by omega]
    simp [List.append_assoc]
  · simp [Int.natCast_add, Int.natCast_mul]
    omega

/-- General positive-u Junc transition: one alternating pair is moved from
    the left parameter to the middle parameter, with net head displacement -2. -/
theorem juncPos_next_delta (u v w : Nat) (hw : 2 ≤ w) :
    runWithDelta (4*v+10) (junc (u+1) v w) =
      some (junc u (v+2) (w-2), -2) := by
  have hmid := juncPos_to_midA_delta u v w (by omega)
  have hones : ones (w-1) = true :: ones (w-2) := by
    cases w with
    | zero => omega
    | succ w => cases w with
      | zero => omega
      | succ w => rfl
  rw [show 4*v+10 = (2*v+6) + 2*(v+2) by omega, runWithDelta_add, hmid]
  simp only [Option.bind_some]
  have hinput : midApos u v w =
      z 0 (true :: (ones (2*(v+2)) ++ (pairs01 u ++ ones 5))) true
        (true :: (ones (w-2) ++ [false,true])) := by
    simp [midApos, hones, List.append_assoc, List.cons_append]
  have hshift :
      runWithDelta (2*(v+2)) (midApos u v w) =
        some (junc u (v+2) (w-2), -((2*(v+2) : Nat) : Int)) := by
    rw [hinput]
    simpa [junc, pairs01, List.append_assoc, List.cons_append] using
      (shift_A11_delta (v+2) (pairs01 u ++ ones 5) (ones (w-2) ++ [false,true]))
  rw [hshift]
  simp only [Option.map_some]
  simp [Int.natCast_add, Int.natCast_mul]
  omega

/-- Total step count for N full positive-u Junc transitions, with the
    middle parameter increasing by two after each transition. -/
def juncPosFullTime : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, v => 4*v+10 + juncPosFullTime n (v+2)

/-- Iterating N positive-u Junc transitions decreases u and w by 1 and 2
    respectively, increases v by 2, and moves the head left by 2N. -/
theorem juncPos_iter_full_delta (N U v w : Nat) (hU : N ≤ U) (hw : 2*N ≤ w) :
    runWithDelta (juncPosFullTime N v) (junc U v w) =
      some (junc (U-N) (v+2*N) (w-2*N), -((2*N : Nat) : Int)) := by
  induction N generalizing U v w with
  | zero => rfl
  | succ N ih =>
      have hstep0 := juncPos_next_delta (U-1) v w (by omega)
      have hstep : runWithDelta (4*v+10) (junc U v w) =
          some (junc (U-1) (v+2) (w-2), -2) := by
        simpa [Nat.sub_add_cancel (by omega : 1 ≤ U)] using hstep0
      rw [show juncPosFullTime (N+1) v = (4*v+10) + juncPosFullTime N (v+2) by rfl,
        runWithDelta_add, hstep]
      simp only [Option.bind_some]
      have htail := ih (U-1) (v+2) (w-2) (by omega) (by omega)
      rw [htail]
      simp only [Option.map_some]
      have hUsub : U-1-N = U-(N+1) := by omega
      have hv : v+2+2*N = v+2*(N+1) := by omega
      have hwsub : w-2-2*N = w-2*(N+1) := by omega
      rw [hUsub, hv, hwsub]
      simp [junc, Int.natCast_add, Int.natCast_mul]
      omega

/-- Number of steps to reach the intermediate A configuration on the Nth
    positive-u Junc transition (N>=1). -/
def juncPosMidTime : Nat → Nat → Nat
  | 0, _ => 0
  | 1, v => 2*v+6
  | n+2, v => 4*v+10 + juncPosMidTime (n+1) (v+2)

/-- After N positive-u Junc transitions, the Nth intermediate A head is
    exactly 2v+2N cells to the right of the initial Junc head. -/
theorem juncPos_iter_mid_delta (N U v w : Nat) (hN : 1 ≤ N)
    (hU : N ≤ U) (hw : 2*N-1 ≤ w) :
    runWithDelta (juncPosMidTime N v) (junc U v w) =
      some (midApos (U-N) (v+2*(N-1)) (w-2*(N-1)), ((2*v+2*N : Nat) : Int)) := by
  cases N with
  | zero => omega
  | succ N =>
      induction N generalizing U v w with
      | zero =>
          have hstep := juncPos_to_midA_delta (U-1) v w (by omega)
          simpa [juncPosMidTime, midApos, Nat.sub_add_cancel (by omega : 1 ≤ U)] using hstep
      | succ N ih =>
          have hstep0 := juncPos_next_delta (U-1) v w (by omega)
          have hstep : runWithDelta (4*v+10) (junc U v w) =
              some (junc (U-1) (v+2) (w-2), -2) := by
            simpa [Nat.sub_add_cancel (by omega : 1 ≤ U)] using hstep0
          rw [show juncPosMidTime (N+2) v = (4*v+10) + juncPosMidTime (N+1) (v+2) by rfl,
            runWithDelta_add, hstep]
          simp only [Option.bind_some]
          have htail := ih (U-1) (v+2) (w-2) (by omega) (by omega) (by omega)
          rw [htail]
          simp only [Option.map_some]
          simp only [Nat.succ_sub_one]
          have hUsub : U-1-(N+1) = U-(N+2) := by omega
          have hv : v+2+2*N = v+2*(N+1) := by omega
          have hwsub : w-2-2*N = w-2*(N+1) := by omega
          rw [hUsub, hv, hwsub]
          simp [midApos, Int.natCast_add, Int.natCast_mul]
          omega


/-- After the two positive-u transitions from the even-b finish_C entry,
    the u=0 Junc transition reaches a later head at net offset +11. -/
theorem sourceScanE_finishC_even_after_junc0_delta (r k : Nat) (hk : 3 ≤ k) :
    runWithDelta
      ((crossTime (2*r)+1 + (12+2*(2*r))) +
        (juncPosFullTime 2 (2*r+2) + (2*(2*r+6)+27)))
      (sourceScanE (2*r) (sourceSuffix k)) =
      some (junc (2*r+9) 0 (2*k-6), 11) := by
  rw [runWithDelta_add, sourceScanE_finishC_even_delta]
  simp only [Option.bind_some]
  rw [runWithDelta_add,
    juncPos_iter_full_delta 2 2 (2*r+2) (2*k+1) (by omega) (by omega)]
  simp only [Option.bind_some]
  have hcfg : junc (2-2) (2*r+2+2*2) (2*k+1-2*2) =
      junc 0 (2*r+6) (2*k-3) := by
    congr 1 <;> omega
  rw [hcfg, junc0_next_delta (2*r+6) (2*k-3) (by omega)]
  have hwout : (2*k-3)-3 = 2*k-6 := by omega
  rw [hwout]
  simp only [Option.map_some]
  simp [Int.natCast_add, Int.natCast_mul]
  omega

/-- For even b=2r and 6<=k<=b+14, the repeated positive-u Junc excursion
    reaches a head strictly beyond the entire 2k-cell shift interval. -/
theorem sourceScanE_finishC_even_long_delta (r k : Nat) (hk : 6 ≤ k)
    (hbound : k ≤ 2*r+14) :
    runWithDelta
      (((crossTime (2*r)+1 + (12+2*(2*r))) +
        (juncPosFullTime 2 (2*r+2) + (2*(2*r+6)+27))) + juncPosMidTime (k-5) 0)
      (sourceScanE (2*r) (sourceSuffix k)) =
      some (midApos ((2*r+9)-(k-5)) (2*((k-5)-1))
        ((2*k-6)-2*((k-5)-1)), ((2*k+1 : Nat) : Int)) := by
  rw [runWithDelta_add, sourceScanE_finishC_even_after_junc0_delta r k (by omega)]
  simp only [Option.bind_some]
  rw [juncPos_iter_mid_delta (k-5) (2*r+9) 0 (2*k-6)
    (by omega) (by omega) (by omega)]
  simp only [Option.map_some]
  simp [Int.natCast_add, Int.natCast_mul]
  omega

/-- The odd-b path followed by N positive-u transitions has a rightward
    intermediate excursion of +7+2N from the post-shift S_E boundary. -/
theorem sourceScanE_finishC_odd_long_delta (r k : Nat) (hk : 4 ≤ k)
    (hbound : k ≤ 2*r+9) :
    runWithDelta
      (((crossTime (2*r+1)+1 + (12+2*(2*r+1))) + (2*(2*r+3)+27)) +
        juncPosMidTime (k-3) 0)
      (sourceScanE (2*r+1) (sourceSuffix k)) =
      some (midApos ((2*r+6)-(k-3)) (2*((k-3)-1))
        ((2*k-2)-2*((k-3)-1)), ((2*k+1 : Nat) : Int)) := by
  rw [runWithDelta_add, sourceScanE_finishC_odd_next_delta r k (by omega)]
  simp only [Option.bind_some]
  have hwstart : (2*k+1)-3 = 2*k-2 := by omega
  rw [hwstart]
  rw [juncPos_iter_mid_delta (k-3) (2*r+6) 0 (2*k-2)
    (by omega) (by omega) (by omega)]
  simp only [Option.map_some]
  simp [Int.natCast_add, Int.natCast_mul]
  omega

/-- Physical lift of the even long-parameter crossing certificate. -/
theorem physical_sourceScanE_finishC_even_long_delta (r k : Nat) (hk : 6 ≤ k)
    (hbound : k ≤ 2*r+14) (c : Config)
    (hrep : Represents (sourceScanE (2*r) (sourceSuffix k)) c) :
    ∃ c', BB6Coverage.run target429
      (((crossTime (2*r)+1 + (12+2*(2*r))) +
        (juncPosFullTime 2 (2*r+2) + (2*(2*r+6)+27))) + juncPosMidTime (k-5) 0) c = some c' ∧
      Represents (midApos ((2*r+9)-(k-5)) (2*((k-5)-1))
        ((2*k-6)-2*((k-5)-1))) c' ∧ c'.head = c.head + (2*k+1) := by
  obtain ⟨c', hrun, hrep', hhead⟩ :=
    BB429DeltaPhysicalBridge.source_runWithDelta_rep
      (((crossTime (2*r)+1 + (12+2*(2*r))) +
        (juncPosFullTime 2 (2*r+2) + (2*(2*r+6)+27))) + juncPosMidTime (k-5) 0)
      (sourceScanE (2*r) (sourceSuffix k)) c hrep
      (midApos ((2*r+9)-(k-5)) (2*((k-5)-1))
        ((2*k-6)-2*((k-5)-1))) ((2*k+1 : Nat) : Int)
      (sourceScanE_finishC_even_long_delta r k hk hbound)
  have hhead' : c'.head = c.head + (2*k+1) := by
    simpa [Int.natCast_add, Int.natCast_mul] using hhead
  exact ⟨c', hrun, hrep', hhead'⟩

/-- Physical lift of the odd long-parameter crossing certificate. -/
theorem physical_sourceScanE_finishC_odd_long_delta (r k : Nat) (hk : 4 ≤ k)
    (hbound : k ≤ 2*r+9) (c : Config)
    (hrep : Represents (sourceScanE (2*r+1) (sourceSuffix k)) c) :
    ∃ c', BB6Coverage.run target429
      (((crossTime (2*r+1)+1 + (12+2*(2*r+1))) + (2*(2*r+3)+27)) +
        juncPosMidTime (k-3) 0) c = some c' ∧
      Represents (midApos ((2*r+6)-(k-3)) (2*((k-3)-1))
        ((2*k-2)-2*((k-3)-1))) c' ∧ c'.head = c.head + (2*k+1) := by
  obtain ⟨c', hrun, hrep', hhead⟩ :=
    BB429DeltaPhysicalBridge.source_runWithDelta_rep
      (((crossTime (2*r+1)+1 + (12+2*(2*r+1))) + (2*(2*r+3)+27)) +
        juncPosMidTime (k-3) 0)
      (sourceScanE (2*r+1) (sourceSuffix k)) c hrep
      (midApos ((2*r+6)-(k-3)) (2*((k-3)-1))
        ((2*k-2)-2*((k-3)-1))) ((2*k+1 : Nat) : Int)
      (sourceScanE_finishC_odd_long_delta r k hk hbound)
  have hhead' : c'.head = c.head + (2*k+1) := by
    simpa [Int.natCast_add, Int.natCast_mul] using hhead
  exact ⟨c', hrun, hrep', hhead'⟩


/-- Physical lift of the even-b +11 excursion after the two positive-u
    transitions and the u=0 Junc transition. -/
theorem physical_sourceScanE_finishC_even_after_junc0_delta (r k : Nat)
    (hk : 3 ≤ k) (c : Config)
    (hrep : Represents (sourceScanE (2*r) (sourceSuffix k)) c) :
    ∃ c', BB6Coverage.run target429
      ((crossTime (2*r)+1 + (12+2*(2*r))) +
        (juncPosFullTime 2 (2*r+2) + (2*(2*r+6)+27))) c = some c' ∧
      Represents (junc (2*r+9) 0 (2*k-6)) c' ∧ c'.head = c.head + 11 := by
  obtain ⟨c', hrun, hrep', hhead⟩ :=
    BB429DeltaPhysicalBridge.source_runWithDelta_rep
      ((crossTime (2*r)+1 + (12+2*(2*r))) +
        (juncPosFullTime 2 (2*r+2) + (2*(2*r+6)+27)))
      (sourceScanE (2*r) (sourceSuffix k)) c hrep
      (junc (2*r+9) 0 (2*k-6)) 11
      (sourceScanE_finishC_even_after_junc0_delta r k hk)
  exact ⟨c', hrun, hrep', hhead⟩

end BB429JuncHeadExcursion

#print axioms BB429JuncHeadExcursion.junc2_to_midA_delta
#print axioms BB429JuncHeadExcursion.junc0_next_delta
#print axioms BB429JuncHeadExcursion.sourceScanE_finishC_even_midA_delta
#print axioms BB429JuncHeadExcursion.sourceScanE_finishC_odd_next_delta
#print axioms BB429JuncHeadExcursion.physical_sourceScanE_finishC_even_midA_delta
#print axioms BB429JuncHeadExcursion.physical_sourceScanE_finishC_odd_next_delta

#print axioms BB429JuncHeadExcursion.juncPos_iter_full_delta
#print axioms BB429JuncHeadExcursion.juncPos_iter_mid_delta
#print axioms BB429JuncHeadExcursion.sourceScanE_finishC_even_after_junc0_delta
#print axioms BB429JuncHeadExcursion.sourceScanE_finishC_even_long_delta
#print axioms BB429JuncHeadExcursion.sourceScanE_finishC_odd_long_delta
#print axioms BB429JuncHeadExcursion.physical_sourceScanE_finishC_even_long_delta
#print axioms BB429JuncHeadExcursion.physical_sourceScanE_finishC_odd_long_delta
#print axioms BB429JuncHeadExcursion.physical_sourceScanE_finishC_even_after_junc0_delta
