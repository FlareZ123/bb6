import Mathlib

namespace BB6.Agent20AdjacentReflection

/-- The all-residue reflection identity is *exact over integers*.
    For adjacent-label modulus M=2L+3, it implies that changing the
    predecessor label L maps the other-label potential r to c-r. -/
theorem reflection_identity {L B P a d : Int}
    (edge : L*B=(L+3)*P+d) :
    3*((3*P+a)+(3*B+a)-2*(a-d)) =
      (2*L+3)*((3*B+a)-(3*P+a)) := by
  linear_combination -6*edge

/-- The mod-3 multiple of the reflected potential is always divisible
    by the adjacent-label modulus; cancellation uses its odd power-of-2 form. -/
theorem reflection_triple_dvd {L B P a d : Int}
    (edge : L*B=(L+3)*P+d) :
    (2*L+3) ∣ 3*((3*P+a)+(3*B+a)-2*(a-d)) := by
  exact ⟨(3*B+a)-(3*P+a), reflection_identity edge⟩

private theorem two_pow_dominates_index (v : Nat) : v ≤ 2^v := by
  induction v with
  | zero => decide
  | succ n ih =>
      have hs : (2:Nat)^(n+1)=2*2^n := by
        rw [pow_succ]
        ring
      have hp : 0<(2:Nat)^n := pow_pos (by decide) _
      rw [hs]
      omega

/-- The reflection offset is nonzero for every natural v: there is no
    one-step upward recurrence, even for valuation zero or one. -/
theorem adjacent_offset_nonzero (v : Nat) :
    ¬ ((2^(v+2)+3 : Nat) ∣ 2^(v+1)*(2*v+1)) := by
  have hodd : Odd (2^(v+2)+3) := by
    refine ⟨2^(v+1)+1, ?_⟩
    rw [pow_succ]
    omega
  have hcop : (2^(v+1)).Coprime (2^(v+2)+3) :=
    (Nat.coprime_two_left.mpr hodd).pow_left (v+1)
  have hlarge : 2*v+1 < 2^(v+2)+3 := by
    have hv := two_pow_dominates_index v
    have hs : (2:Nat)^(v+2) = 4*2^v := by
      rw [pow_succ, pow_succ]
      ring
    rw [hs]
    omega
  intro h
  have hdiv : (2^(v+2)+3) ∣ 2*v+1 :=
    hcop.dvd_of_dvd_mul_left h
  have hlow : 2^(v+2)+3 ≤ 2*v+1 :=
    Nat.le_of_dvd (by omega) hdiv
  omega

#print axioms reflection_identity
#print axioms reflection_triple_dvd
#print axioms adjacent_offset_nonzero
end BB6.Agent20AdjacentReflection
