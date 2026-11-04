import Root119BGrowFinal
import Root119BShield
namespace BB6Root119

theorem shiftMany_head (n : Nat) (c : Conf) :
    (shiftMany n c).h = c.h - 2*(n:Int) := by
  induction n generalizing c with
  | zero => simp [shiftMany]
  | succ n ih =>
    change (shiftMany n (shifted c)).h = c.h - 2*((n+1:Int))
    rw [ih (shifted c)]
    change c.h - 2 - 2*(n:Int) = c.h - 2*((n+1:Int))
    omega

theorem shiftMany_farLeft (n : Nat) (c : Conf) (x : Int)
    (hx : x ≤ c.h - 2*(n:Int) - 3) :
    (shiftMany n c).tape x = c.tape x := by
  induction n generalizing c with
  | zero => simp [shiftMany]
  | succ n ih =>
    have hx' : x ≤ (shifted c).h - 2*(n:Int) - 3 := by
      change x ≤ c.h - 2 - 2*(n:Int) - 3
      omega
    have h0 : (shiftMany (n+1) c).tape x = (shiftMany n (shifted c)).tape x := by rfl
    rw [h0, ih (shifted c) hx']
    exact shiftTape_left c.tape c.h x (by omega)

theorem shiftMany_triple (n : Nat) (c : Conf) (hv : extended n c) :
    extended 0 (shiftMany n c) := by
  induction n generalizing c with
  | zero => simpa [shiftMany] using hv
  | succ n ih =>
    exact ih (shifted c) (shifted_extended c hv)

def fourZeroBoundary (n : Nat) (c : Conf) : Prop :=
  c.tape (c.h-2*(n:Int)-4) = false ∧
  c.tape (c.h-2*(n:Int)-5) = false ∧
  c.tape (c.h-2*(n:Int)-6) = false ∧
  c.tape (c.h-2*(n:Int)-7) = false

theorem growHyp_after_shift (n : Nat) (c : Conf)
    (he : extended n c) (hz : fourZeroBoundary n c) :
    growHyp (shiftMany n c).tape (shiftMany n c).h := by
  obtain ⟨h0,h1,h2,h3,hrest⟩ := shiftMany_triple n c he
  have head := shiftMany_head n c
  obtain ⟨z4,z5,z6,z7⟩ := hz
  change (shiftMany n c).q = .B at h0
  change (shiftMany n c).tape (shiftMany n c).h = false at h1
  change (shiftMany n c).tape ((shiftMany n c).h-1) = true at h2
  change (shiftMany n c).tape ((shiftMany n c).h-2) = true at h3
  have h3bit : (shiftMany n c).tape ((shiftMany n c).h-3) = true := hrest.1
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa using h1
  · exact h2
  · exact h3
  · exact h3bit
  · change (shiftMany n c).tape ((shiftMany n c).h-4) = false
    rw [head]
    rw [shiftMany_farLeft n c (c.h-2*(n:Int)-4) (by omega)]
    exact z4
  · change (shiftMany n c).tape ((shiftMany n c).h-5) = false
    rw [head]
    rw [shiftMany_farLeft n c (c.h-2*(n:Int)-5) (by omega)]
    exact z5
  · change (shiftMany n c).tape ((shiftMany n c).h-6) = false
    rw [head]
    rw [shiftMany_farLeft n c (c.h-2*(n:Int)-6) (by omega)]
    exact z6
  · change (shiftMany n c).tape ((shiftMany n c).h-7) = false
    rw [head]
    rw [shiftMany_farLeft n c (c.h-2*(n:Int)-7) (by omega)]
    exact z7

theorem fullSweep (n : Nat) (c : Conf)
    (he : extended n c) (hz : fourZeroBoundary n c) :
    run (10*n+16) c =
      some ⟨.B,(shiftMany n c).h-8,
        growTape (shiftMany n c).tape (shiftMany n c).h⟩ := by
  rw [run_add, ten_n_steps n c he]
  change run 16 (shiftMany n c) = _
  have hh : (shiftMany n c).q = .B := (shiftMany_triple n c he).1
  have hg := growHyp_after_shift n c he hz
  cases hC : shiftMany n c with
  | mk q h t =>
    have hb : q = .B := by simpa [hC] using hh
    have he : growHyp t h := by simpa [hC] using hg
    cases q <;> try contradiction
    simpa [hC] using grow16 t h he

#print axioms BB6Root119.fullSweep
end BB6Root119
