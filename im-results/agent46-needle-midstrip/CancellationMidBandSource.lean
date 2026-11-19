import CancellationMidBand
import CancellationMidBandResidue
import CancellationTerminalConstructive
import NeedleGeneralInverseSource
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46.CancellationMidBandSource
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle
open CancellationGap CancellationConstructive CancellationTerminalConstructive CancellationMidBand CancellationMidBandResidue
open NeedleInverse NeedleGeneralInverse

/-- The odd-tail factorization is unique: its valuation and odd quotient are
    determined by the represented counter. -/
theorem oddTower_injective (q₁ v₁ q₂ v₂ : Nat)
    (h : oddTower q₁ v₁ = oddTower q₂ v₂) :
    q₁=q₂ ∧ v₁=v₂ := by
  induction v₁ generalizing q₁ q₂ v₂ with
  | zero =>
      cases v₂ with
      | zero =>
          simp [oddTower] at h
          omega
      | succ v₂ =>
          have hleft : oddTower q₁ 0 % 2 = 1 := by simp [oddTower]
          have hright : oddTower q₂ (v₂+1) % 2 = 0 := by simp [oddTower]
          have hm := congrArg (fun n => n%2) h
          rw [hleft, hright] at hm
          omega
  | succ v₁ ih =>
      cases v₂ with
      | zero =>
          have hleft : oddTower q₁ (v₁+1) % 2 = 0 := by simp [oddTower]
          have hright : oddTower q₂ 0 % 2 = 1 := by simp [oddTower]
          have hm := congrArg (fun n => n%2) h
          rw [hleft, hright] at hm
          omega
      | succ v₂ =>
          have h' : 2*(oddTower q₁ v₁+1) = 2*(oddTower q₂ v₂+1) := by
            simpa [oddTower] using h
          have hbase : oddTower q₁ v₁ = oddTower q₂ v₂ := by
            have hc := Nat.mul_left_cancel (by decide : 0<2) h'
            omega
          have hh := ih q₁ q₂ v₂ hbase
          exact ⟨hh.1, by omega⟩

/-- Every member of the exact inverse-parent list for the synthetic feeder
    avoids the contiguous valuation band. -/
theorem feeder_parent_not_in_midband
    (r s q' u' : Nat)
    (hr : 2 ≤ r)
    (hs : cancellation_threshold r ≤ s)
    (hc : (2*r-2)*s ≤ valuationA r-cancellation_threshold r)
    (hmem : (u',q') ∈ NeedleGeneralInverse.parents
      (oddTower (feederQ r) (feederV r)+2)) :
    u' ≠ valuationA r-1+s := by
  intro hu
  have ha : 1 ≤ valuationA r := by
    have h := valuationA_linear r
    omega
  have huBig : 2 ≤ u' := by
    rw [hu]
    have h := valuationA_linear r
    omega
  have hparent := (NeedleGeneralInverse.parents_spec q' u'
    (oddTower (feederQ r) (feederV r)+2)).mp hmem
  have hparent' :
      oddTower (feederQ r) (feederV r)+2 =
        (2^(u'+1)+3)*q' + (3*2^u' + u' + 3) := by
    simpa [NeedleInverse.den, NeedleInverse.bias] using hparent
  have hf := oddTower_factor (feederQ r) (feederV r)
  have hv : feederV r+1=valuationA r := by
    dsimp [feederV]
    omega
  have hpow : 2^(valuationA r)=2*2^(feederV r) := by
    rw [←hv, Nat.pow_succ]
    simp [Nat.mul_comm]
  have hparentEq :
      2^(valuationA r)*(2*feederQ r+3) =
        (2^(u'+1)+3)*(2*q'+3)+(2*u'-3) := by
    calc
      2^(valuationA r)*(2*feederQ r+3)
          = 2*(2^(feederV r)*(2*feederQ r+3)) := by
              rw [hpow]
              simp [Nat.mul_assoc, Nat.mul_comm]
      _ = 2*(oddTower (feederQ r) (feederV r)+2) := by
              rw [←hf]
      _ = 2*((2^(u'+1)+3)*q'+3*2^u'+u'+3) := by
              have hmul := congrArg (fun x => 2*x) hparent'
              simpa [Nat.add_assoc] using hmul
      _ = (2^(u'+1)+3)*(2*q'+3)+(2*u'-3) := by
              have hpowU : 2^(u'+1)=2*2^u' := by
                rw [Nat.pow_succ]
                simp [Nat.mul_comm]
              rw [hpowU]
              simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
              omega
  have hdiv :
      (2^(u'+1)+3) ∣
        (2^(valuationA r)*(2*feederQ r+3)+3-2*u') := by
    refine ⟨2*q'+3, ?_⟩
    omega
  have hno := CancellationMidBand.midband_no_parent_source_equation
    r s (feederQ r) hr hs hc (feeder_equation r (by omega))
  have hdiv' :
      (2^(valuationA r+s)+3) ∣
        (2^(valuationA r)*(2*feederQ r+3)+3-
          2*(valuationA r-1+s)) := by
    simpa [hu, show (valuationA r-1+s)+1=valuationA r+s by omega] using hdiv
  exact hno hdiv'

/-- A genuine original-source predecessor cannot enter the feeder from a
    valuation in the middle band. The source inverse equivalence is the
    complete inverse characterization of the pinned high-level transition. -/
theorem no_original_source_parent_in_midband
    (r s q' u' : Nat)
    (hr : 2 ≤ r)
    (hs : cancellation_threshold r ≤ s)
    (hc : (2*r-2)*s ≤ valuationA r-cancellation_threshold r)
    (hu : u'=valuationA r-1+s) :
    highLevelNext (.N (oddTower q' u')) ≠
      some (.N (oddTower (feederQ r) (feederV r))) := by
  intro hsrc
  rcases (BB6.Agent20.SpaceNeedleGeneralInverse.original_source_inverse_iff
    (oddTower q' u') (oddTower (feederQ r) (feederV r))).mp hsrc with
      ⟨q₀,u₀,hd,hmem⟩
  have hinj := oddTower_injective q' u' q₀ u₀ hd
  rcases hinj with ⟨hq,hv⟩
  subst q₀
  subst u₀
  exact (feeder_parent_not_in_midband r s q' u' hr hs hc hmem) hu


/-- Every exact inverse parent in the new residue-dependent band is excluded. -/
theorem feeder_parent_not_in_remainder_band
    (r s q' u' : Nat)
    (hr : 2 ≤ r)
    (hs : cancellation_threshold r ≤ s)
    (hcase : valuationA r ≤ (2*r-1)*s)
    (hupper : r*s ≤ valuationA r)
    (hrem : cancellation_threshold r ≤ cutRemainder (valuationA r) s)
    (hmem : (u',q') ∈ NeedleGeneralInverse.parents
      (oddTower (feederQ r) (feederV r)+2)) :
    u' ≠ valuationA r-1+s := by
  intro hu
  have hparent := (NeedleGeneralInverse.parents_spec q' u'
    (oddTower (feederQ r) (feederV r)+2)).mp hmem
  have hparent' :
    oddTower (feederQ r) (feederV r)+2 =
      (2^(u'+1)+3)*q' + (3*2^u' + u' + 3) := by
    simpa [NeedleInverse.den, NeedleInverse.bias] using hparent
  have hf := oddTower_factor (feederQ r) (feederV r)
  have hv : feederV r+1=valuationA r := by
    dsimp [feederV]
    omega
  have hpow : 2^(valuationA r)=2*2^(feederV r) := by
    rw [←hv, Nat.pow_succ]
    simp [Nat.mul_comm]
  have hparentEq :
    2^(valuationA r)*(2*feederQ r+3) =
      (2^(u'+1)+3)*(2*q'+3)+(2*u'-3) := by
    calc
      2^(valuationA r)*(2*feederQ r+3)
          = 2*(2^(feederV r)*(2*feederQ r+3)) := by
              rw [hpow]
              simp [Nat.mul_assoc, Nat.mul_comm]
      _ = 2*(oddTower (feederQ r) (feederV r)+2) := by
              rw [←hf]
      _ = 2*((2^(u'+1)+3)*q'+3*2^u'+u'+3) := by
              have hmul := congrArg (fun x => 2*x) hparent'
              simpa [Nat.add_assoc] using hmul
      _ = (2^(u'+1)+3)*(2*q'+3)+(2*u'-3) := by
              have hpowU : 2^(u'+1)=2*2^u' := by
                rw [Nat.pow_succ]
                simp [Nat.mul_comm]
              rw [hpowU]
              simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
              omega
  have hdiv :
    (2^(u'+1)+3) ∣
      (2^(valuationA r)*(2*feederQ r+3)+3-2*u') := by
    refine ⟨2*q'+3, ?_⟩
    omega
  have hno := midband_no_parent_remainder_source_equation
    r s (feederQ r) hr hs hcase hupper hrem
    (feeder_equation r (by omega))
  have hdiv' :
    (2^(valuationA r+s)+3) ∣
      (2^(valuationA r)*(2*feederQ r+3)+3-
        2*(valuationA r-1+s)) := by
    simpa [hu, show (valuationA r-1+s)+1=valuationA r+s by omega] using hdiv
  exact hno hdiv'

/-- Original-source form of the residue-dependent immediate-parent exclusion. -/
theorem no_original_source_parent_in_remainder_band
    (r s q' u' : Nat)
    (hr : 2 ≤ r)
    (hs : cancellation_threshold r ≤ s)
    (hcase : valuationA r ≤ (2*r-1)*s)
    (hupper : r*s ≤ valuationA r)
    (hrem : cancellation_threshold r ≤ cutRemainder (valuationA r) s)
    (hu : u'=valuationA r-1+s) :
    highLevelNext (.N (oddTower q' u')) ≠
      some (.N (oddTower (feederQ r) (feederV r))) := by
  intro hsrc
  rcases (BB6.Agent20.SpaceNeedleGeneralInverse.original_source_inverse_iff
    (oddTower q' u') (oddTower (feederQ r) (feederV r))).mp hsrc with
      ⟨q₀,u₀,hd,hmem⟩
  have hinj := oddTower_injective q' u' q₀ u₀ hd
  rcases hinj with ⟨hq,hv⟩
  subst q₀
  subst u₀
  exact (feeder_parent_not_in_remainder_band r s q' u' hr hs hcase hupper hrem hmem) hu


/-- Wider cut-exponent version: no exact source parent can have a valuation
    whose cut exponent exceeds the logarithmic threshold by at least one. -/
theorem feeder_parent_not_in_remainder_band_wide
    (r s q' u' : Nat)
    (hr : 2 ≤ r)
    (hs : cancellation_threshold r ≤ s)
    (hcase : valuationA r ≤ (2*r-1)*s)
    (hrem : cancellation_threshold r ≤ cutRemainder (valuationA r) s)
    (hE : cancellation_threshold r+1 ≤
      2*valuationA r-(2*r-2)*s-cutRemainder (valuationA r) s)
    (hmem : (u',q') ∈ NeedleGeneralInverse.parents
      (oddTower (feederQ r) (feederV r)+2)) :
    u' ≠ valuationA r-1+s := by
  intro hu
  have hparent := (NeedleGeneralInverse.parents_spec q' u'
    (oddTower (feederQ r) (feederV r)+2)).mp hmem
  have hparent' :
    oddTower (feederQ r) (feederV r)+2 =
      (2^(u'+1)+3)*q' + (3*2^u' + u' + 3) := by
    simpa [NeedleInverse.den, NeedleInverse.bias] using hparent
  have hf := oddTower_factor (feederQ r) (feederV r)
  have hv : feederV r+1=valuationA r := by
    dsimp [feederV]
    omega
  have hpow : 2^(valuationA r)=2*2^(feederV r) := by
    rw [←hv, Nat.pow_succ]
    simp [Nat.mul_comm]
  have hparentEq :
    2^(valuationA r)*(2*feederQ r+3) =
      (2^(u'+1)+3)*(2*q'+3)+(2*u'-3) := by
    calc
      2^(valuationA r)*(2*feederQ r+3)
          = 2*(2^(feederV r)*(2*feederQ r+3)) := by
              rw [hpow]
              simp [Nat.mul_assoc, Nat.mul_comm]
      _ = 2*(oddTower (feederQ r) (feederV r)+2) := by
              rw [←hf]
      _ = 2*((2^(u'+1)+3)*q'+3*2^u'+u'+3) := by
              have hmul := congrArg (fun x => 2*x) hparent'
              simpa [Nat.add_assoc] using hmul
      _ = (2^(u'+1)+3)*(2*q'+3)+(2*u'-3) := by
              have hpowU : 2^(u'+1)=2*2^u' := by
                rw [Nat.pow_succ]
                simp [Nat.mul_comm]
              rw [hpowU]
              simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
              omega
  have hdiv :
    (2^(u'+1)+3) ∣
      (2^(valuationA r)*(2*feederQ r+3)+3-2*u') := by
    refine ⟨2*q'+3, ?_⟩
    omega
  have hno := midband_no_parent_remainder_general_source_equation
    r s (feederQ r) hr hs hcase hrem hE
    (feeder_equation r (by omega))
  have hdiv' :
    (2^(valuationA r+s)+3) ∣
      (2^(valuationA r)*(2*feederQ r+3)+3-
        2*(valuationA r-1+s)) := by
    simpa [hu, show (valuationA r-1+s)+1=valuationA r+s by omega] using hdiv
  exact hno hdiv'


/-- The wider residue-dependent exclusion is lifted through the complete
    original-source inverse equivalence. -/
theorem no_original_source_parent_in_remainder_band_wide
    (r s q' u' : Nat)
    (hr : 2 ≤ r)
    (hs : cancellation_threshold r ≤ s)
    (hcase : valuationA r ≤ (2*r-1)*s)
    (hrem : cancellation_threshold r ≤ cutRemainder (valuationA r) s)
    (hE : cancellation_threshold r+1 ≤
      2*valuationA r-(2*r-2)*s-cutRemainder (valuationA r) s)
    (hu : u'=valuationA r-1+s) :
    highLevelNext (.N (oddTower q' u')) ≠
      some (.N (oddTower (feederQ r) (feederV r))) := by
  intro hsrc
  rcases (BB6.Agent20.SpaceNeedleGeneralInverse.original_source_inverse_iff
    (oddTower q' u') (oddTower (feederQ r) (feederV r))).mp hsrc with
      ⟨q₀,u₀,hd,hmem⟩
  have hinj := oddTower_injective q' u' q₀ u₀ hd
  rcases hinj with ⟨hq,hv⟩
  subst q₀
  subst u₀
  exact (feeder_parent_not_in_remainder_band_wide r s q' u' hr hs hcase hrem hE hmem) hu

#print axioms feeder_parent_not_in_remainder_band
#print axioms no_original_source_parent_in_remainder_band
#print axioms feeder_parent_not_in_remainder_band_wide
#print axioms no_original_source_parent_in_remainder_band_wide

#print axioms oddTower_injective
#print axioms feeder_parent_not_in_midband
#print axioms no_original_source_parent_in_midband
end BB6.Agent46.CancellationMidBandSource
