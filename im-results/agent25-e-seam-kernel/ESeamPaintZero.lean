import ESeamNoReturn

namespace BB6.PhysicalWindow

def paint (c : Physical) : Physical := { c with bits := c.bits ||| 1 }

/-- The protected marker bit is unaffected by painting the unvisited cell 0. -/
theorem paint_marker (c : Physical) : (paint c).bits.testBit 1 = c.bits.testBit 1 := by
  simp [paint, Nat.testBit_or, Nat.testBit_one_eq_true_iff_self_eq_zero]

/-- No machine scan at a positive position can observe the low unvisited bit. -/
theorem paint_scan (c : Physical) (hp : 1 ≤ c.pos) :
    scanned (paint c) = scanned c := by
  unfold scanned cell paint
  by_cases hw : c.pos < 18
  · simp only [hw, ↓reduceIte, Nat.testBit_or]
    have hneq : c.pos ≠ 0 := by omega
    simp [Nat.testBit_one_eq_true_iff_self_eq_zero, hneq]
  · simp [hw]

/-- A write in the protected window at position >=2 commutes with painting
    the untouched low bit; exact source transition semantics. -/
theorem paint_update (c : Physical) (wr : Nat) (hp : 2 ≤ c.pos) (hwin : c.pos < 18) :
    updatedBits (paint c) wr = (updatedBits c wr) ||| 1 := by
  have hsmall : 1 <<< c.pos < 2 ^ 18 := by
    simpa [Nat.shiftLeft_eq] using
      (Nat.pow_lt_pow_right (by omega : 1 < 2) hwin)
  have hmask : (1 <<< c.pos).testBit 0 = false := by
    simpa [Nat.shiftLeft_eq] using
      (Nat.testBit_two_pow_of_ne (n := c.pos) (m := 0) (by omega))
  have hcomp : 262143 - (1 <<< c.pos) = 2 ^ 18 - ((1 <<< c.pos)+1) := by
    have h18 : 2 ^ 18 = 262144 := by decide
    omega
  have hcomp0 : (262143 - (1 <<< c.pos)).testBit 0 = true := by
    rw [hcomp, Nat.testBit_two_pow_sub_succ hsmall 0]
    simp [hmask]
  have hand : 1 &&& (262143 - (1 <<< c.pos)) = 1 := by
    have hmod : (262143 - (1 <<< c.pos)) % 2 = 1 := by
      simpa only [Nat.testBit_zero, decide_eq_true_eq] using hcomp0
    simpa only [Nat.one_and_eq_mod_two] using hmod
  unfold updatedBits paint
  split
  · change (c.bits ||| 1) ||| (1 <<< c.pos) =
      (c.bits ||| (1 <<< c.pos)) ||| 1
    ac_rfl
  · change (c.bits ||| 1) &&& (262143 - (1 <<< c.pos)) =
      (c.bits &&& (262143 - (1 <<< c.pos))) ||| 1
    rw [Nat.and_or_distrib_right, hand]

private theorem leading_false (a b d e : Bool)
    (h : (b && d && e) = false) :
    (a && b && d && e) = false := by
  cases a <;> cases b <;> cases d <;> cases e <;> simp_all

private theorem terminal_nof0 (c : Physical)
    (hp : 2 ≤ c.pos) (hb : c.bits.testBit 1 = true) :
    terminal c = (c.pos == 1 || (c.state == 5 && scanned c == 1)) := by
  have hn := no_F0_before_marker c hp hb
  have hg := leading_false (decide (c.pos < 18)) (c.state == 5)
    (scanned c == 0) (c.bits.land ((1 <<< c.pos) - 1) == 0) hn
  simp only [terminal, hg, Bool.or_false]

/-- The stopped-event predicate is unaffected by the unvisited bit zero. -/
theorem paint_terminal (c : Physical) (hwf : WellFormed c)
    (hbit : c.bits.testBit 1 = true) :
    terminal (paint c) = terminal c := by
  rcases hwf with ⟨hst, hb, hp⟩
  by_cases hm : c.pos = 1
  · simp [terminal, paint, hm]
  have hp2 : 2 ≤ c.pos := by omega
  have hpaint := paint_marker c
  have hnoPaint : (paint c).bits.testBit 1 = true := by
    rw [hpaint]
    exact hbit
  rw [terminal_nof0 c hp2 hbit,
    terminal_nof0 (paint c) (by simpa [paint] using hp2) hnoPaint]
  change (c.pos == 1 || (c.state == 5 && scanned (paint c) == 1)) =
    (c.pos == 1 || (c.state == 5 && scanned c == 1))
  rw [paint_scan c hp]

/- The remaining step is to compose paint_update and paint_terminal into
   complete step-conjugacy. That result is intentionally not asserted. -/
#print axioms paint_scan
#print axioms paint_update
#print axioms terminal_nof0
#print axioms paint_terminal
end BB6.PhysicalWindow
