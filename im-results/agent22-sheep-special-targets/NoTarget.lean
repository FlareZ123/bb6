import EvenEdge
import SpecialSourceGap
import NoGenericTarget

namespace Agent22Special

/-- Exact all-k missing-incoming family for the genuine first-even Sheep
    section relation. Includes both special and generic source laws. -/
theorem no_even_edge_to_3pow (k x : Nat) :
    ¬ SheepEven.EvenEdge x (3*2^(4*k+2)) := by
  intro hedge
  obtain ⟨z,h,u,hs,hz5,hu,hz,hy⟩ := hedge
  have hzero : h=0 := triple_target_odd_block_zero (4*k+2) h u hy
  subst h
  have hz' : z = 3*2^(4*k+2) := by
    simp only [Nat.pow_zero, Nat.one_mul] at hz hy
    omega
  cases hs with
  | special a =>
    by_cases ha : a=0
    · subst a
      simp only [Nat.pow_zero, Nat.mul_one] at hz'
      have hpow : (2:Nat)^2 ≤ 2^(4*k+2) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · exact no_special_source (4*k+2) a (by omega) hz'.symm
  | generic a v hv hmin =>
    have hformula : 2*(1+2^0*u)+1 = ((2:Nat)^(a+1)+1)*v+2*a := by
      rw [← hz, Nat.pow_succ]
      grind
    have hpow : (2:Nat)^(4*k+3)=2^(4*k+2)*2 := by
      rw [show 4*k+3=(4*k+2)+1 by omega, Nat.pow_succ]
    have heq : ((2:Nat)^(a+1)+1)*v+2*a = 3*2^(4*k+3)+1 := by
      simp only [Nat.pow_zero, Nat.one_mul] at hformula
      have huval : 1+u=3*2^(4*k+2) := by omega
      rw [huval] at hformula
      rw [hpow]
      omega
    exact no_generic_target_any k a v heq

#print axioms no_even_edge_to_3pow
end Agent22Special
