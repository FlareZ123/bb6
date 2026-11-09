import PhysicalWindow

namespace BB6.PhysicalWindow

/-- The terminal marker bit is not modified when the head stays to its right. -/
theorem updatedBits_bit1 (c : Physical) (wr : Nat)
    (hp : 2 ≤ c.pos) (hb : c.bits.testBit 1 = true) (hwin : c.pos < 18) :
    (updatedBits c wr).testBit 1 = true := by
  have hmask : (1 <<< c.pos).testBit 1 = false := by
    simpa [Nat.shiftLeft_eq] using
      (Nat.testBit_two_pow_of_ne (n := c.pos) (m := 1) (by omega))
  have hsmall : 1 <<< c.pos < 2 ^ 18 := by
    simpa [Nat.shiftLeft_eq] using
      (Nat.pow_lt_pow_right (by omega : 1 < 2) hwin)
  have h18 : 2 ^ 18 = 262144 := by decide
  have hcomp : 262143 - (1 <<< c.pos) = 2 ^ 18 - ((1 <<< c.pos) + 1) := by
    omega
  unfold updatedBits
  split
  · change (c.bits ||| (1 <<< c.pos)).testBit 1 = true
    simp [hb, hmask]
  · change (c.bits &&& (262143 - (1 <<< c.pos))).testBit 1 = true
    rw [Nat.testBit_and, hb]
    simp only [Bool.true_and]
    rw [hcomp, Nat.testBit_two_pow_sub_succ hsmall 1]
    simp [hmask]

/-- Before the protected marker is reached, the terminal 1 at offset 1 persists. -/
theorem step_preserves_bit1 (c : Physical)
    (hwf : WellFormed c) (hbit : c.bits.testBit 1 = true) :
    (step c).bits.testBit 1 = true := by
  rcases hwf with ⟨hst, hb, hp⟩
  by_cases hterm : terminal c = true
  · simpa [step, hterm] using hbit
  have ht : terminal c = false := Bool.eq_false_iff.mpr hterm
  have hn6 : c.state ≠ 6 := by omega
  have hp1 : c.pos ≠ 1 := by
    intro h1
    exact hterm (terminal_at_marker c h1)
  have hp2 : 2 ≤ c.pos := by omega
  by_cases hw : c.pos < 18
  · simpa [step, ht, hn6, hw] using
      updatedBits_bit1 c (table c.state (scanned c)).1 hp2 hbit hw
  · simpa [step, ht, hn6, hw] using hbit

theorem marker_bit1_all_times (c : Physical)
    (hwf : WellFormed c) (hmarker : c.bits.testBit 1 = true) (t : Nat) :
    (run t c).bits.testBit 1 = true := by
  induction t generalizing c with
  | zero => exact hmarker
  | succ n ih =>
      simpa [run] using ih (step c) (wellformed_step c hwf)
        (step_preserves_bit1 c hwf hmarker)

/-- Every physically blank-left F/0 event must follow marker contact:
    offset 1 stays 1 and is strictly left of every live position >= 2. -/
theorem no_F0_before_marker (c : Physical) (hp : 2 ≤ c.pos)
    (hmarker : c.bits.testBit 1 = true) :
    (c.state == 5 && scanned c == 0 &&
      c.bits.land ((1 <<< c.pos) - 1) == 0) = false := by
  have hm : ((1 <<< c.pos) - 1).testBit 1 = true := by
    simp [Nat.shiftLeft_eq, Nat.testBit_two_pow_sub_one,
      show 1 < c.pos by omega]
  have hnonzero : c.bits.land ((1 <<< c.pos) - 1) ≠ 0 := by
    intro hz
    have ht : (c.bits.land ((1 <<< c.pos)-1)).testBit 1 = true := by
      simpa [Nat.testBit_and, hmarker, hm]
    rw [hz] at ht
    contradiction
  have hz : (c.bits.land ((1 <<< c.pos) - 1) == 0) = false :=
    beq_eq_false_iff_ne.mpr hnonzero
  simp only [hz, Bool.and_false]

/-- Every physical E boundary with arbitrary right tape retains its left
    marker until its very first encounter; no earlier blank-left return exists. -/
theorem seed_no_F0_before_marker (r : Nat) (remote : Nat → Bool)
    (hr : r < 128) (t : Nat) (hp : 2 ≤ (run t (seed r remote)).pos) :
    ((run t (seed r remote)).state == 5 &&
      scanned (run t (seed r remote)) == 0 &&
      (run t (seed r remote)).bits.land
        ((1 <<< (run t (seed r remote)).pos) - 1) == 0) = false := by
  have hseedbit : (seed r remote).bits.testBit 1 = true := by
    change (171 + 2048 * r).testBit 1 = true
    rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
    omega
  exact no_F0_before_marker _ hp
    (marker_bit1_all_times (seed r remote)
      (seed_wellformed r remote hr) hseedbit t)

#print axioms updatedBits_bit1
#print axioms step_preserves_bit1
#print axioms marker_bit1_all_times
#print axioms no_F0_before_marker
#print axioms seed_no_F0_before_marker

end BB6.PhysicalWindow
