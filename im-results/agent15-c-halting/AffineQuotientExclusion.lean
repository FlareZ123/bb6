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

end BB6.Agent15
