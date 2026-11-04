import ExactGate
import SurvivingSmall

namespace CascadeSurvivingGate
open CascadeSource CascadeSweep

/-- Convert a source-episode reverse-inductive orbit into concatenable form. -/
theorem orbit_trans {x y z : Nat × Nat}
    (h : Orbit x y) (g : Orbit y z) : Orbit x z := by
  induction h with
  | refl => exact g
  | step hc ht ih => exact Orbit.step hc (ih g)

/-- The existing source-C forward closure is included in the all-time
    reachability relation certified by the weighted-mass checker. -/
theorem reachable_to_orbit {x y : Nat × Nat}
    (h : ReachC x y) : Orbit x y := by
  induction h with
  | refl => exact Orbit.refl _
  | push hs he ih =>
      exact orbit_trans ih (Orbit.step he (Orbit.refl _))

/-- Genuine post-initial blank root cannot reach a surviving-class
    fatal reset with index at most 47. -/
theorem no_surviving_reset_through_47 (n : Nat)
    (hn : n ≤ 47) (hc : n%6=4 ∨ n%6=5) :
    ¬ReachC (2,0) (4*2^n-n-4,0) := by
  intro h
  have hh := blank_excludes_survivors_through_47 n hn hc
  exact hh (reachable_to_orbit h)

/-- Strengthened complete necessary/sufficient gate for halting from
    #746's post-initial source-indexed C(2,0): the first surviving
    possible fatal exponent is 52, rather than the previous bound 6. -/
theorem halt_iff_surviving_index_ge_52 :
    (∃ a, ReachC (2,0) (a,1)) ↔
    (∃ n, 52≤n ∧ (n%6=4 ∨ n%6=5) ∧
      ReachC (2,0) (4*2^n-n-4,0)) := by
  constructor
  · intro h
    obtain ⟨n,_,hc,hr⟩ := CascadeExactGate.halt_iff_complementary_reached.mp h
    have hn : 52≤n := by
      by_contra hlow
      have hsmall : n≤47 := by omega
      exact no_surviving_reset_through_47 n hsmall hc hr
    exact ⟨n,hn,hc,hr⟩
  · rintro ⟨n,hn,hc,hr⟩
    apply CascadeExactGate.halt_iff_complementary_reached.mpr
    exact ⟨n,by omega,hc,hr⟩

#print axioms no_surviving_reset_through_47
#print axioms halt_iff_surviving_index_ge_52

end CascadeSurvivingGate
