import AdaptiveFiniteTransfer
import GenericCritical41K

namespace BB6.Agent8AdaptiveP1
open BB6.Agent8Adaptive

/-- One finite source-certified pair of shadow graph certificates at q0 proves
an entire 2-adic family of ORIGINAL blank P1 critical gateway exclusions.
There is no dependence on a chosen lifted path length. -/
theorem all_lifted_gateways_excluded_adaptive
    (D q0 r M : Nat) (hq : 29≤q0) (hM : M≤41) (hD : M≤D)
    (base0 base1 : List (Nat × Nat))
    (hroot0 : (0,12*q0+4)∈base0)
    (hroot1 : (0,10*q0+4)∈base1)
    (hclosed0 : ∀ m z t v zp, (m,z)∈base0 → z=2^t*v →
        2*zp+1=16*q0+8+m+t+v → (m+t+1,zp)∈base0)
    (hclosed1 : ∀ m z t v zp, (m,z)∈base1 → z=2^t*v →
        2*zp+1=16*q0+9+m+t+v → (m+t+1,zp)∈base1)
    (hsmall0 : ∀ m z, (m,z)∈base0 → m≤M)
    (hsmall1 : ∀ m z, (m,z)∈base1 → m≤M)
    (hstate0 : ∀ m z, (m,z)∈base0 → ¬2^(D-m)∣z)
    (hstate1 : ∀ m z, (m,z)∈base1 → ¬2^(D-m)∣z)
    (hnodiv0 : ∀ m z, (m,z)∈base0 → ¬1024∣z)
    (hnodiv1 : ∀ m z, (m,z)∈base1 → ¬1024∣z) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(q0+2^D*r)+2)-2*(16*(q0+2^D*r)+2)-10) := by
  let q := q0+2^D*r
  have hbound0 : 12*q0+4+2^D*(12*r) ≤
      (16*q0+8+16*2^D*r)+M := by
    have hh : 2^D*(12*r) = 12*(2^D*r) := by ac_rfl
    rw [hh]
    have hh2 : 16*2^D*r = 16*(2^D*r) := by ac_rfl
    rw [hh2]
    omega
  have hbound1 : 10*q0+4+2^D*(10*r) ≤
      (16*q0+9+16*2^D*r)+M := by
    have hh : 2^D*(10*r) = 10*(2^D*r) := by ac_rfl
    rw [hh]
    have hh2 : 16*2^D*r = 16*(2^D*r) := by ac_rfl
    rw [hh2]
    omega
  obtain ⟨nodes0,root0,closed0,small0,nodiv0⟩ :=
    finite_adaptive_transfer D M (16*q0+8) (12*q0+4) 12 r
       base0 hroot0 hclosed0 hsmall0 hD hstate0 hnodiv0 hbound0
  obtain ⟨nodes1,root1,closed1,small1,nodiv1⟩ :=
    finite_adaptive_transfer D M (16*q0+9) (10*q0+4) 10 r
       base1 hroot1 hclosed1 hsmall1 hD hstate1 hnodiv1 hbound1
  have heq0 : 12*q+4=(12*q0+4)+2^D*(12*r) := by
    dsimp [q]
    rw [Nat.mul_add]
    ac_rfl
  have heq1 : 10*q+4=(10*q0+4)+2^D*(10*r) := by
    dsimp [q]
    rw [Nat.mul_add]
    ac_rfl
  have hs0 : (0,12*q+4)∈nodes0 := by simpa only [heq0] using root0
  have hs1 : (0,10*q+4)∈nodes1 := by simpa only [heq1] using root1
  have hc0 : ∀ m z t v zp, (m,z)∈nodes0 → z=2^t*v →
      2*zp+1=16*q+8+m+t+v → (m+t+1,zp)∈nodes0 := by
    intro m z t v zp hm hd hnn
    have heq : 16*q+8=(16*q0+8)+16*2^D*r := by
      dsimp [q]
      rw [Nat.mul_add]
      ac_rfl
    apply closed0 m z t v zp hm hd
    simpa only [heq] using hnn
  have hc1 : ∀ m z t v zp, (m,z)∈nodes1 → z=2^t*v →
      2*zp+1=16*q+9+m+t+v → (m+t+1,zp)∈nodes1 := by
    intro m z t v zp hm hd hnn
    have heq : 16*q+9=(16*q0+9)+16*2^D*r := by
      dsimp [q]
      rw [Nat.mul_add]
      ac_rfl
    apply closed1 m z t v zp hm hd
    simpa only [heq] using hnn
  have hd0 : ∀ m z, (m,z)∈nodes0 → ¬1024∣z := nodiv0
  have hd1 : ∀ m z, (m,z)∈nodes1 → ¬1024∣z := nodiv1
  have small41_0 : ∀ m z, (m,z)∈nodes0 → m≤41 := by
    intro m z h
    have := small0 m z h
    omega
  have small41_1 : ∀ m z, (m,z)∈nodes1 → m≤41 := by
    intro m z h
    have := small1 m z h
    omega
  exact BB6.Agent9Generic41K.critical_unreachable_of_shadow41K q
    (by dsimp [q]; omega) nodes0 nodes1 hs0 hs1 hc0 hc1 small41_0 small41_1 hd0 hd1

#print axioms all_lifted_gateways_excluded_adaptive
end BB6.Agent8AdaptiveP1
