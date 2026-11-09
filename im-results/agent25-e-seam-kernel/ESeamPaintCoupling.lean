import ESeamPaintZero

namespace BB6.PhysicalWindow

theorem paint_step (c : Physical) (hwf : WellFormed c)
    (hbit : c.bits.testBit 1 = true) :
    step (paint c) = paint (step c) := by
  have heq := paint_terminal c hwf hbit
  have hs := paint_scan c hwf.2.2
  simp only [step, heq, hs]
  have hpos : (paint c).pos = c.pos := rfl
  have hstate : (paint c).state = c.state := rfl
  have hremote : (paint c).remote = c.remote := rfl
  simp only [hpos,hstate,hremote]
  by_cases hstop : (terminal c || c.state == 6) = true
  · simp only [hstop, ↓reduceIte]
  · have hstopFalse : (terminal c || c.state == 6) = false := Bool.eq_false_iff.mpr hstop
    simp only [hstopFalse, Bool.false_eq_true, ↓reduceIte]
    have ht0 : terminal c = false := by
      cases htc : terminal c <;> simp_all
    have hp1 : c.pos ≠ 1 := by
      intro h
      have hmark := terminal_at_marker c h
      simp [hmark] at ht0
    have hp2 : 2 ≤ c.pos := by
      have hp := hwf.2.2
      omega
    by_cases hw : c.pos < 18
    · have hu := paint_update c (table c.state (scanned c)).fst hp2 hw
      rw [hu]
      simp [paint, hw]
    · simp [paint, hw]
      rfl

/-- Arbitrarily long physical runs are conjugate under the low-bit projection. -/
theorem paint_run (c : Physical) (hwf : WellFormed c)
    (hbit : c.bits.testBit 1 = true) (t : Nat) :
    run t (paint c) = paint (run t c) := by
  induction t generalizing c with
  | zero => rfl
  | succ n ih =>
      simpa [run, paint_step c hwf hbit] using
        ih (step c) (wellformed_step c hwf) (step_preserves_bit1 c hwf hbit)

def seed0 (r : Nat) (remote : Nat → Bool) : Physical :=
  {pos := 10, state := 4, bits := 170+2048*r, remote := remote}

theorem seed0_wf (r : Nat) (remote : Nat → Bool) (hr : r < 128) :
    WellFormed (seed0 r remote) := by
  simp [WellFormed, seed0]
  omega

theorem seed0_marker1 (r : Nat) (remote : Nat → Bool) :
    (seed0 r remote).bits.testBit 1 = true := by
  change (170+2048*r).testBit 1 = true
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
  omega

theorem paint_seed0 (r : Nat) (remote : Nat → Bool) :
    paint (seed0 r remote) = seed r remote := by
  have hm : (170+2048*r)%2=0 := by omega
  have hdiv : ((170+2048*r)|||1)/2 = (170+2048*r)/2 := by
    rw [Nat.or_div_two]
    simp
  have hmod : ((170+2048*r)|||1)%2=1 := by
    rw [Nat.or_mod_two]
    simp [hm]
  have heq : ((170+2048*r)|||1) =171+2048*r := by omega
  simp [paint, seed0, seed, heq]

#print axioms paint_step
#print axioms paint_run
#print axioms paint_seed0

end BB6.PhysicalWindow
