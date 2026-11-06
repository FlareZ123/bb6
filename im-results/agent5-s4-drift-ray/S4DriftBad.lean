import S4Toggle
import Lean.Elab.Tactic.Omega

namespace S4DriftBad
open S4Power S4Octet S4Toggle
set_option maxHeartbeats 0

/-- A concrete immediately failing completion of the second stationary triple. -/
theorem bad_halt_witness : P [284,1646,1021,1] = none := by
  simp [P,G,H]

/-- An infinite parametric class of source P-halts sharing the other fixed
    three-digit projection; the suffix may be arbitrary. -/
theorem bad_halt_family (x : Nat) (S : List Nat)
    (hx : Pow2 (x+1023+2*W S)) :
    P ([284,1646,1021,x]++S)=none := by
  obtain ⟨n, hn⟩ := hx
  have hw : W ([284,1646,1021,x]++S)+509=8*(x+1023+2*W S) := by
    simp [W]
    omega
  have hp : Pow2 (W ([284,1646,1021,x]++S)+509) := by
    refine ⟨n+3, ?_⟩
    rw [hw,hn]
    simp [Nat.pow_add, Nat.mul_comm]
  have hg : G 509 ([284,1646,1021,x]++S)=none :=
    (G_none_iff_power 509 _ (by omega)).mpr hp
  unfold P
  rw [hg]
  rfl

#print axioms bad_halt_witness
#print axioms bad_halt_family
end S4DriftBad
