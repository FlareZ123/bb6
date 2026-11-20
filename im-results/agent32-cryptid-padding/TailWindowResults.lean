import TailWindowCore

namespace TailWindow

open Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

def haltCheck (n q b maxRight : Nat) : Bool :=
  match run (n - 1) (some (startLocal q b)) with
  | none => false
  | some c =>
      match step c with
      | none => false
      | some d =>
          decide (d.state = 5 ∧ d.tape d.pos = true ∧ step d = none) &&
            within n (some (startLocal q b)) (-5) (maxRight : Int)

theorem empty_suffix_113 : haltCheck 113 0 0 10 = true := by decide
theorem suffix_01_127 : haltCheck 127 1 0 13 = true := by decide
theorem suffix_011_74 : haltCheck 74 1 1 12 = true := by decide
theorem suffix_0101011_131 : haltCheck 131 3 1 16 = true := by decide
theorem suffix_010101011_153 : haltCheck 153 4 1 18 = true := by decide

theorem haltCheck_sound (n q b maxRight : Nat) (hn : 0 < n)
    (hcheck : haltCheck n q b maxRight = true) :
    ∃ d, run n (some (startLocal q b)) = some d ∧
      d.state = 5 ∧ d.tape d.pos = true ∧ step d = none ∧
      Stays (-5) (maxRight : Int) n (some (startLocal q b)) := by
  unfold haltCheck at hcheck
  cases hr : run (n - 1) (some (startLocal q b)) with
  | none => simp [hr] at hcheck
  | some c0 =>
      cases hs : step c0 with
      | none => simp [hr, hs] at hcheck
      | some d =>
          simp only [hr, hs] at hcheck
          have hparts := Bool.and_eq_true_iff.mp hcheck
          rcases hparts with ⟨hdec, hwithin⟩
          have ⟨hstate, hhead, hhalt⟩ := of_decide_eq_true hdec
          have hlocal : run n (some (startLocal q b)) = some d := by
            rw [← Nat.sub_add_cancel hn, run_succ_right]
            simp [hr, hs]
          exact ⟨d, hlocal, hstate, hhead, hhalt,
            (within_iff_Stays (-5) (maxRight : Int) n
              (some (startLocal q b))).1 hwithin⟩

theorem actualTail_halts (n q b maxRight m : Nat) (hn : 0 < n)
    (hcheck : haltCheck n q b maxRight = true) (hm : 3 ≤ m) :
    ∃ c, run n (some (startActual m q b)) = some c ∧
      c.state = 5 ∧ c.tape c.pos = true ∧ step c = none := by
  obtain ⟨d, hlocal, hstate, hhead, hhalt, hstay⟩ :=
    haltCheck_sound n q b maxRight hn hcheck
  have hEq0 : OptionEqOn (-5) (maxRight : Int)
      (some (startLocal q b)) (some (startActual m q b)) := by
    rcases initialEqOn m q b maxRight hm with ⟨hs, hp, ht⟩
    exact ⟨hs.symm, hp.symm, fun i hlo hhi => (ht i hlo hhi).symm⟩
  have hrunEq := runEqOn (-5) (maxRight : Int) n
    (some (startLocal q b)) (some (startActual m q b)) hEq0 hstay
  rw [hlocal] at hrunEq
  cases hrun : run n (some (startActual m q b)) with
  | none => simp only [hrun, OptionEqOn] at hrunEq
  | some c =>
      simp only [hrun, OptionEqOn] at hrunEq
      change ConfigEqOn (-5) (maxRight : Int) d c at hrunEq
      rcases hrunEq with ⟨hstate', hpos, htape⟩
      have hwin : -5 ≤ d.pos ∧ d.pos ≤ (maxRight : Int) := by
        simpa [hlocal] using
          (stays_run_pos (-5) (maxRight : Int) n
            (some (startLocal q b)) hstay)
      have hread : c.tape c.pos = d.tape d.pos := by
        rw [← hpos]
        exact (htape d.pos hwin.1 hwin.2).symm
      have hcstate : c.state = 5 := hstate'.symm.trans hstate
      refine ⟨c, rfl, hcstate, ?_, ?_⟩
      · rw [hread]
        exact hhead
      · simp [step, hcstate, hread, hhead, instr]

theorem actual_empty_suffix_113 (m : Nat) (hm : 3 ≤ m) :
    ∃ c, run 113 (some (startActual m 0 0)) = some c ∧
      c.state = 5 ∧ c.tape c.pos = true ∧ step c = none := by
  exact actualTail_halts 113 0 0 10 m (by decide) empty_suffix_113 hm

theorem actual_suffix_01_127 (m : Nat) (hm : 3 ≤ m) :
    ∃ c, run 127 (some (startActual m 1 0)) = some c ∧
      c.state = 5 ∧ c.tape c.pos = true ∧ step c = none := by
  exact actualTail_halts 127 1 0 13 m (by decide) suffix_01_127 hm

theorem actual_suffix_011_74 (m : Nat) (hm : 3 ≤ m) :
    ∃ c, run 74 (some (startActual m 1 1)) = some c ∧
      c.state = 5 ∧ c.tape c.pos = true ∧ step c = none := by
  exact actualTail_halts 74 1 1 12 m (by decide) suffix_011_74 hm

theorem actual_suffix_0101011_131 (m : Nat) (hm : 3 ≤ m) :
    ∃ c, run 131 (some (startActual m 3 1)) = some c ∧
      c.state = 5 ∧ c.tape c.pos = true ∧ step c = none := by
  exact actualTail_halts 131 3 1 16 m (by decide) suffix_0101011_131 hm

theorem actual_suffix_010101011_153 (m : Nat) (hm : 3 ≤ m) :
    ∃ c, run 153 (some (startActual m 4 1)) = some c ∧
      c.state = 5 ∧ c.tape c.pos = true ∧ step c = none := by
  exact actualTail_halts 153 4 1 18 m (by decide) suffix_010101011_153 hm

#print axioms actual_empty_suffix_113
#print axioms actual_suffix_01_127
#print axioms actual_suffix_011_74
#print axioms actual_suffix_0101011_131
#print axioms actual_suffix_010101011_153

end TailWindow
