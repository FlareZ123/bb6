import M8M16Composition
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15

/-- The four original-source quotient cylinders, tested after complete
    affine normalization. -/
abbrev affineQuotientCondition (a k : Nat) : Prop :=
  let p := affineNormalize a k
  (p.1%8=7 ∧ p.2%8=4) ∨
  (p.1%8=1 ∧ p.2%16=2) ∨
  (p.1%16=9 ∧ p.2%16=15) ∨
  (p.1%16=1 ∧ p.2%16=7 ∧ (p.1≠1 ∨ p.2≠7))

/-- Executable one-sided filter combining the earlier affine arithmetic
    exclusions with the source-verified M8/M16 quotient cylinders. -/
def affineQuotientExcluded (a k : Nat) : Bool :=
  affineExcluded a k || decide (affineQuotientCondition a k)

/-- Soundness of the combined decidable filter for authentic blank-origin
    section reachability. -/
theorem affineQuotientExcluded_sound (a k : Nat)
    (hex : affineQuotientExcluded a k = true) :
    ¬ CReach a k := by
  intro hreach
  unfold affineQuotientExcluded at hex
  rcases Bool.or_eq_true_iff.mp hex with hbasic | hquot
  · exact (affineExcluded_sound a k hbasic) hreach
  · have hnorm := (reach_iff_normalize a k).mp hreach
    cases hp : affineNormalize a k with
    | mk x y =>
      rw [hp] at hnorm
      have hq :
          (x%8=7 ∧ y%8=4) ∨
          (x%8=1 ∧ y%16=2) ∨
          (x%16=9 ∧ y%16=15) ∨
          (x%16=1 ∧ y%16=7 ∧ (x≠1 ∨ y≠7)) := by
        simpa [affineQuotientCondition, hp] using of_decide_eq_true hquot
      rcases hq with hM8 | hM16A | hM16B | hM16C
      · have hx : x=8*(x/8)+7 := by omega
        have hy : y=8*(y/8)+4 := by omega
        rw [hx,hy] at hnorm
        exact blank_no_m8_cylinder (x/8) (y/8) hnorm
      · have hx : x=8*(x/8)+1 := by omega
        have hy : y=16*(y/16)+2 := by omega
        rw [hx,hy] at hnorm
        exact blank_no_m16_one_two_cylinder (x/8) (y/16) hnorm
      · have hx : x=16*(x/16)+9 := by omega
        have hy : y=16*(y/16)+15 := by omega
        rw [hx,hy] at hnorm
        exact blank_no_m16_nine_fifteen_cylinder (x/16) (y/16) hnorm
      · have hx : x=16*(x/16)+1 := by omega
        have hy : y=16*(y/16)+7 := by omega
        have hpos : 0<x/16 ∨ 0<y/16 := by omega
        rw [hx,hy] at hnorm
        exact blank_no_m16_one_seven_cylinder (x/16) (y/16) hpos hnorm

#print axioms affineQuotientExcluded_sound

/-- Every reachable section input is rejected by neither branch of the
    sound one-sided filter. -/
theorem affineQuotientExcluded_false_of_reachable (a k : Nat)
    (hreach : CReach a k) :
    affineQuotientExcluded a k = false := by
  cases hq : affineQuotientExcluded a k with
  | false => rfl
  | true =>
      exact False.elim ((affineQuotientExcluded_sound a k hq) hreach)

/-- Exact Machine C blank-halting gateway with the source-verified quotient
    filter attached as a necessary condition on each normalized parameter
    family. The filter is executable; the remaining reachability predicate
    is still the unresolved mathematical problem. -/
theorem blank_halts_iff_filtered_normalized_families :
    BB6.CReachBridge.RunHalts ↔
      (∃ m k, k+3*m+4=2^(2*m+3) ∧
         CReach (affineNormalize 1 k).1 (affineNormalize 1 k).2 ∧
         affineQuotientExcluded 1 k = false) ∨
      (∃ j m k, k+j+3*m+5=2^(2*m+2)*(j+3) ∧
         CReach (affineNormalize (2*j+3) k).1
           (affineNormalize (2*j+3) k).2 ∧
         affineQuotientExcluded (2*j+3) k = false) := by
  rw [blank_halts_iff_normalized_families]
  constructor
  · rintro (h1 | h2)
    · rcases h1 with ⟨m,k,heq,hreach⟩
      have hsource : CReach 1 k :=
        (reach_iff_normalize 1 k).mpr hreach
      exact Or.inl ⟨m,k,heq,hreach,
        affineQuotientExcluded_false_of_reachable 1 k hsource⟩
    · rcases h2 with ⟨j,m,k,heq,hreach⟩
      have hsource : CReach (2*j+3) k :=
        (reach_iff_normalize (2*j+3) k).mpr hreach
      exact Or.inr ⟨j,m,k,heq,hreach,
        affineQuotientExcluded_false_of_reachable (2*j+3) k hsource⟩
  · rintro (h1 | h2)
    · rcases h1 with ⟨m,k,heq,hreach,_⟩
      exact Or.inl ⟨m,k,heq,hreach⟩
    · rcases h2 with ⟨j,m,k,heq,hreach,_⟩
      exact Or.inr ⟨j,m,k,heq,hreach⟩

#print axioms blank_halts_iff_filtered_normalized_families

end BB6.Agent15
