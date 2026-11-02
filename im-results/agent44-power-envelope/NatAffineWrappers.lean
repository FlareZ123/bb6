import PowerCertificate
import GOneSource

set_option maxRecDepth 4096

namespace BB6.Agent44

/-- A Nat-coefficient wrapper for every even-coordinate 14-power leaf. -/
theorem nat_power_leaf
    (q R x A C : Nat) (hR : 21≤R)
    (hAlo : 65832≤A) (hAhi : A≤130896)
    (hClo : 8≤C) (hChi : C≤130290)
    (hshape : x+12 = A*(7*2^(65536*q+R-16)-(q+1))+C) :
    ∀ j : Nat, x+12 ≠ 14*2^j := by
  have hAloInt : (65832:Int)≤A := Int.ofNat_le.mpr hAlo
  have hAhiInt : (A:Int)≤130896 := Int.ofNat_le.mpr hAhi
  have hCloInt : (8:Int)≤C := Int.ofNat_le.mpr hClo
  have hChiInt : (C:Int)≤130290 := Int.ofNat_le.mpr hChi
  have hc : ((x+12:Nat):Int) =
      ((A*(7*2^(65536*q+R-16)-(q+1))+C:Nat):Int) :=
    congrArg (fun n:Nat => (n:Int)) hshape
  have hx : ((x+12:Nat):Int) =
      (A:Int)*((7*2^(65536*q+R-16)-(q+1)):Nat)+(C:Int) := by
    simpa only [Int.natCast_add, Int.natCast_mul] using hc
  exact p1_affine_leaf_no_power q R x A C hR
    hAloInt hAhiInt hCloInt hChiInt hx

/-- Nat-coefficient wrapper for the exceptional GAncestor input 1. -/
theorem nat_no_one_ancestor
    (q R b d A C : Nat) (hR : 30≤R)
    (hcase : (65536≤A ∧ A≤74888 ∧ 12≤C ∧ C≤74562) ∨
             (74928≤A ∧ A≤130720 ∧ 10≤C ∧ C≤130036))
    (hshape : d+b/2+3 = A*(7*2^(65536*q+R-16)-(q+1))+C) :
    ∀ k, ¬BB6.P1Reduction.GAncestor b d k 1 := by
  have hc := congrArg (fun n:Nat => (n:Int)) hshape
  have hx : ((d+b/2+3:Nat):Int) =
      (A:Int)*((7*2^(65536*q+R-16)-(q+1)):Nat)+(C:Int) := by
    simpa only [Int.natCast_add, Int.natCast_mul] using hc
  have hcaseInt :
      (65536≤(A:Int) ∧ (A:Int)≤74888 ∧ 12≤(C:Int) ∧ (C:Int)≤74562) ∨
      (74928≤(A:Int) ∧ (A:Int)≤130720 ∧ 10≤(C:Int) ∧ (C:Int)≤130036) := by
    rcases hcase with ⟨a,b,c,d⟩ | ⟨a,b,c,d⟩
    · exact Or.inl ⟨Int.ofNat_le.mpr a,Int.ofNat_le.mpr b,
        Int.ofNat_le.mpr c,Int.ofNat_le.mpr d⟩
    · exact Or.inr ⟨Int.ofNat_le.mpr a,Int.ofNat_le.mpr b,
        Int.ofNat_le.mpr c,Int.ofNat_le.mpr d⟩
  exact p1_affine_no_one_ancestor q R b d A C hR hcaseInt hx

#print axioms BB6.Agent44.nat_power_leaf
#print axioms BB6.Agent44.nat_no_one_ancestor
end BB6.Agent44
