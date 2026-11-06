import Q74Nodes
import GenericCritical41K

namespace BB6.Agent13Q74
open BB6.Agent9Adaptive

/-- Every exact inverse successor stays inside the affine graph at any r. -/
theorem closed0 (r m z t v zp : Nat)
    (hm : (m,z) ∈ decode r nodes0) (hd : z=2^t*v)
    (hn : 2*zp+1=16*(74+P*r)+8+m+t+v) :
    (m+t+1,zp) ∈ decode r nodes0 := by
  have hn' : 2*zp+1=16*P*r+1192+m+t+v := by
    simp only [Nat.mul_add, Nat.mul_assoc] at hn ⊢
    omega
  exact check_sound 1192 P nodes0 check0 r m z t v zp hm hd hn'

theorem closed1 (r m z t v zp : Nat)
    (hm : (m,z) ∈ decode r nodes1) (hd : z=2^t*v)
    (hn : 2*zp+1=16*(74+P*r)+9+m+t+v) :
    (m+t+1,zp) ∈ decode r nodes1 := by
  have hn' : 2*zp+1=16*P*r+1193+m+t+v := by
    simp only [Nat.mul_add, Nat.mul_assoc] at hn ⊢
    omega
  exact check_sound 1193 P nodes1 check1 r m z t v zp hm hd hn'

theorem bounds0 (r m z : Nat) (hm : (m,z) ∈ decode r nodes0) :
    m≤41 ∧ ¬1024∣z :=
  check_bounds 1192 P nodes0 check0 r m z hm

theorem bounds1 (r m z : Nat) (hm : (m,z) ∈ decode r nodes1) :
    m≤41 ∧ ¬1024∣z :=
  check_bounds 1193 P nodes1 check1 r m z hm

theorem root0 (r : Nat) :
    (0,12*(74+P*r)+4) ∈ decode r nodes0 := by
  apply List.mem_map.mpr
  refine ⟨(0,892,12*P,3), ?_, ?_⟩
  · decide
  · change (0,892+12*P*r)=(0,12*(74+P*r)+4)
    simp [Nat.mul_add, Nat.mul_assoc]
    omega

theorem root1 (r : Nat) :
    (0,10*(74+P*r)+4) ∈ decode r nodes1 := by
  apply List.mem_map.mpr
  refine ⟨(0,744,10*P,4), ?_, ?_⟩
  · decide
  · change (0,744+10*P*r)=(0,10*(74+P*r)+4)
    simp [Nat.mul_add, Nat.mul_assoc]
    omega

/-- All-time original blank-start P1 critical-gateway exclusion.
    Covers n = 1186 + 2^22 * r for every natural r. -/
theorem critical_1186_mod_4194304_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(74+P*r)+2)-2*(16*(74+P*r)+2)-10) := by
  exact BB6.Agent9Generic41K.critical_unreachable_of_shadow41K
    (74+P*r) (by omega) (decode r nodes0) (decode r nodes1)
    (root0 r) (root1 r)
    (closed0 r) (closed1 r)
    (fun m z h => (bounds0 r m z h).1)
    (fun m z h => (bounds1 r m z h).1)
    (fun m z h => (bounds0 r m z h).2)
    (fun m z h => (bounds1 r m z h).2)

#print axioms critical_1186_mod_4194304_unreachable
end BB6.Agent13Q74
