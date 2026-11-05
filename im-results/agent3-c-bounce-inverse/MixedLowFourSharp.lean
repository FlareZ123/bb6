import MixedLowFour
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Stronger all-start statement for every low halting depth m=4 mod8.
    A real one-edge section path reaches the stopping point, but no
    path of length two or greater from ANY starting section state exists. -/
theorem mixed_low_m_four_mod8_sharp (m k : Nat)
    (hm : m%8=4)
    (hstop : k+3*m+4=2^(2*m+3)) :
    (∀ (start : Nat×Nat) (time : Nat),
      BB6.Agent8Section.run secNext (time+2) (some start) ≠ some (1,k)) ∧
    (∃ start : Nat×Nat,
      BB6.Agent8Section.run secNext 1 (some start)=some (1,k)) := by
  have hpow : 8 ∣ 2^(2*m+3) := by
    change 2^3 ∣ 2^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hmod : (k+3*m+4)%8=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hpow
  have hk8 : k%8=0 := by omega
  have hbig : 3*m+24≤2^(2*m+3) := by
    obtain ⟨q,hq⟩ : ∃q : Nat,m=q+1 := ⟨m-1,by omega⟩
    subst m
    exact low_four_pow_extra q
  have hk20 : 20≤k := by omega
  have hedge : secNext (k-1,(k-2)/2)=some (1,k) := by
    apply (BB6.Agent15.section_sum_one_even_iff_affine
      (k-1) ((k-2)/2) 1 k (by omega) (by omega) (by omega)).mpr
    exact ⟨by omega,rfl⟩
  constructor
  · intro start time hh
    have ht : BB6.Agent8Section.run secNext ((time+1)+1) (some start)=
        some (1,k) := by
      simpa only [show (time+1)+1=time+2 by omega] using hh
    change (BB6.Agent8Section.run secNext (time+1) (some start)).bind secNext =
      some (1,k) at ht
    cases hparent : BB6.Agent8Section.run secNext (time+1) (some start) with
    | none => simp [hparent] at ht
    | some p =>
        rcases p with ⟨a,b⟩
        have he : secNext (a,b)=some (1,k) := by simpa [hparent] using ht
        have huni := (BB6.Agent15.section_sum_one_even_iff_affine
          a b 1 k (by omega) (by omega) (by omega)).mp he
        rcases huni with ⟨ha,hb⟩
        rw [ha,hb] at hparent
        change (BB6.Agent8Section.run secNext time (some start)).bind secNext =
          some (k-1,(k-2)/2) at hparent
        cases hprev : BB6.Agent8Section.run secNext time (some start) with
        | none => simp [hprev] at hparent
        | some q =>
            rcases q with ⟨c,d⟩
            have hp : secNext (c,d)=some (k-1,(k-2)/2) := by
              simpa [hprev] using hparent
            have hi := BB6.Agent3.section_odd_image c d (k-1) ((k-2)/2)
              hp (by omega) (by omega)
            omega
  · refine ⟨(k-1,(k-2)/2),?_⟩
    simpa [BB6.Agent8Section.run] using hedge

#print axioms mixed_low_m_four_mod8_sharp
end BB6.Agent3
