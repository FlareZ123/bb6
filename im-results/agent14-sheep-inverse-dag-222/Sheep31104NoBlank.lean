import Sheep31104RootEdge
import Sheep31104ZEdge
import Sheep31104TEdge
import SheepEvenReachInverse

namespace Sheep31104NoBlank

/-- The terminal T affine node is not reachable from Sheep's original
blank-seed first-even state 10, for any parameter k. -/
theorem terminal_T_not_blank (k y : Nat)
    (hy : 31347*y+174404=2^(31117+40824*k)) :
    ¬ SheepEven.EvenReach 10 y := by
  intro hreach
  have hneq : 10 ≠ y := by
    intro heq
    have hpow : (2:Nat)^19 ≤ 2^(31117+40824*k) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have heqpow : (2:Nat)^19 = 524288 := by decide
    rw [heqpow] at hpow
    rw [←heq] at hy
    omega
  obtain ⟨x,hx,hedge⟩ :=
    SheepEvenReachInverse.reach_last_edge hreach hneq
  have hxEven : x%2=0 :=
    SheepEvenReachInverse.even_reach_preserves_even hx (by decide)
  exact Sheep31104TEdge.no_original_edge_into_T k x y hxEven hedge hy

/-- Z has exactly the terminal T affine ancestor and cannot be blank-reached. -/
theorem middle_Z_not_blank (k y : Nat)
    (hy : 3483*y+16576=2^(31114+40824*k)) :
    ¬ SheepEven.EvenReach 10 y := by
  intro hreach
  have hneq : 10 ≠ y := by
    intro heq
    have hpow : (2:Nat)^16 ≤ 2^(31114+40824*k) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have heqpow : (2:Nat)^16 = 65536 := by decide
    rw [heqpow] at hpow
    rw [←heq] at hy
    omega
  obtain ⟨x,hx,hedge⟩ :=
    SheepEvenReachInverse.reach_last_edge hreach hneq
  have hxEven : x%2=0 :=
    SheepEvenReachInverse.even_reach_preserves_even hx (by decide)
  have hT : 31347*x+174404=2^(31117+40824*k) :=
    Sheep31104ZEdge.original_edge_to_Z_has_T_source k x y hxEven hedge hy
  exact (terminal_T_not_blank k x hT) hx

/-- The entire infinite root family j=31104+40824*k is unreachable
in the original source-checked first-even return relation. -/
theorem root_31104_not_blank (k : Nat) :
    ¬ SheepEven.EvenReach 10 (2^(31104+40824*k)) := by
  intro hreach
  have hneq : 10 ≠ 2^(31104+40824*k) := by
    have hpow : (2:Nat)^4 ≤ 2^(31104+40824*k) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have heqpow : (2:Nat)^4 = 16 := by decide
    rw [heqpow] at hpow
    omega
  obtain ⟨x,hx,hedge⟩ :=
    SheepEvenReachInverse.reach_last_edge hreach hneq
  have hxEven : x%2=0 :=
    SheepEvenReachInverse.even_reach_preserves_even hx (by decide)
  have hZ : 3483*x+16576=2^(31114+40824*k) :=
    Sheep31104RootEdge.original_edge_to_root_has_Z_source k x hxEven hedge
  exact (middle_Z_not_blank k x hZ) hx

#print axioms terminal_T_not_blank
#print axioms middle_Z_not_blank
#print axioms root_31104_not_blank
end Sheep31104NoBlank
