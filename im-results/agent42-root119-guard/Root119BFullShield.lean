import Root119BFull
namespace BB6Root119

/-- The growth macro writes only at positions right of its new head. -/
theorem growTape_farLeft (t : Int → Bool) (h x : Int) (hx : x ≤ h-8) :
    growTape t h x = t x := by
  simp [growTape, setBit, show x ≠ h by omega,
    show x ≠ h-1 by omega, show x ≠ h-2 by omega,
    show x ≠ h-4 by omega, show x ≠ h-5 by omega,
    show x ≠ h-6 by omega, show x ≠ h-7 by omega]

/-- Every left-of-B 4-word ban is preserved by 16-step boundary growth. -/
theorem grow_preserves_noLeft4 (p q r : Bool) (c : Conf)
    (hs : NoLeft4 p q r c) :
    NoLeft4 p q r ⟨.B,c.h-8,growTape c.tape c.h⟩ := by
  intro x hx hw
  change x+3 < c.h-8 at hx
  change growTape c.tape c.h x = p ∧ growTape c.tape c.h (x+1) = q ∧
    growTape c.tape c.h (x+2) = r ∧ growTape c.tape c.h (x+3) = false at hw
  have old := hs x (by omega)
  apply old
  refine ⟨?_,?_,?_,?_⟩
  · rw [growTape_farLeft c.tape c.h x (by omega)] at hw
    exact hw.1
  · rw [growTape_farLeft c.tape c.h (x+1) (by omega)] at hw
    exact hw.2.1
  · rw [growTape_farLeft c.tape c.h (x+2) (by omega)] at hw
    exact hw.2.2.1
  · rw [growTape_farLeft c.tape c.h (x+3) (by omega)] at hw
    exact hw.2.2.2

/-- A complete genuine blank-root 10n+16 return preserves any pqr0 ban. -/
theorem fullSweep_reached_safe (p q r : Bool) (n : Nat) (c : Conf)
    (hc : Reach c) (he : extended n c) (hz : fourZeroBoundary n c)
    (hs : NoLeft4 p q r c) :
    let d : Conf := ⟨.B,(shiftMany n c).h-8,
      growTape (shiftMany n c).tape (shiftMany n c).h⟩
    Reach d ∧ NoLeft4 p q r d := by
  dsimp
  constructor
  · exact reachable_of_run (10*n+16) c _ hc (fullSweep n c he hz)
  · exact grow_preserves_noLeft4 p q r (shiftMany n c)
      (shiftMany_preserves_noLeft4 p q r n c he hs)

#print axioms BB6Root119.fullSweep_reached_safe
end BB6Root119
