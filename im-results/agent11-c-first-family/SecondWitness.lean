import SecondUniform
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11
open BB6.Agent15

/-- A nonvacuous all-depth family within the exact second Machine C
    stopping locus. For EVERY depth r and bound L, this constructs
    genuine natural stopping-candidate parameters m≥L,j,k whose section
    state (2j+3,k) is unreachable from the authentic blank entry.
    Original-source CI must certify the imported exclusion theorem. -/
theorem second_halt_unbounded_witness (r lower : Nat) :
    ∃ m j k : Nat, lower≤m ∧ m%4=3 ∧
      k+j+3*m+5=2^(2*m+2)*(j+3) ∧
      ¬CReach (2*j+3) k := by
  let m : Nat := 4*(r+lower)+3
  let P : Nat := 2^(2*r+1)
  let q : Nat := m
  have hm : m%4=3 := by dsimp [m]; omega
  have hr : r+2≤m := by dsimp [m]; omega
  have hmlower : lower≤m := by dsimp [m]; omega
  have hppos : 2≤P := by
    have hpow : 0<2^(2*r) := Nat.pow_pos (by decide)
    have hp : P=2^(2*r)*2 := Nat.pow_succ 2 (2*r)
    omega
  have hsize : 4*m+3 ≤ P*(4*m+1) := by
    have hmul : 2*(4*m+1)≤P*(4*m+1) :=
      Nat.mul_le_mul_right (4*m+1) hppos
    omega
  let j : Nat := P*(4*m+1)-(3*m+3)
  have hj : m≤j := by dsimp [j]; omega
  have hX : j+3*m+3=2^(2*r+1)*(4*m+1) := by
    change j+3*m+3=P*(4*m+1)
    dsimp [j]
    omega
  let H : Nat := 2^(2*m+2)*(j+3)
  have hp8 : 8≤2^(2*m+2) := by
    have he : 2*m+2=3+(2*m-1) := by omega
    rw [he,Nat.pow_add]
    have hpos : 0<2^(2*m-1) := Nat.pow_pos (by decide)
    omega
  have hH : j+3*m+5 ≤ H := by
    have hmul : 8*(j+3) ≤ 2^(2*m+2)*(j+3) :=
      Nat.mul_le_mul_right (j+3) hp8
    dsimp [H]
    omega
  let k : Nat := H-(j+3*m+5)
  have hk : k+j+3*m+5=2^(2*m+2)*(j+3) := by dsimp [k,H]; omega
  refine ⟨m,j,k,hmlower,hm,hk,?_⟩
  exact second_halt_arbitrary_depth m k r j q hm hr (by dsimp [q]; omega)
    (by simpa [q] using hX) hk

#print axioms second_halt_unbounded_witness
end BB6.Agent11
