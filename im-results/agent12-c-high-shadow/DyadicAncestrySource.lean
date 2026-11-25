import DyadicAncestryBridge
import PurePowerRawParent

namespace BB6.Agent12Dyadic
open BB6.Agent12PureFan BB6.Agent46

/-- This is the complete source edge classification, including special
    zero/one-input and small-right outputs. -/
theorem source_edge_contract : EdgeContract secNext := by
  intro a k x y h
  obtain ⟨_,_,hk,hS⟩ := encode_equations x y
  by_cases hy : y<8
  · exact Or.inl (Or.inl ⟨y,hy,hk.symm⟩)
  have hp := (raw_parent_iff a k x y (by omega)).mpr
    ((complete_section_inverse a k x y (by omega)).mp h)
  rcases hp with hd|hz|hone|he|ho
  · obtain ⟨_,ha,hk⟩ := hd
    right
    refine ⟨1,by decide,affine_of_equations a k x y 1 (by decide) (by omega) ?_⟩
    simp; omega
  · obtain ⟨_,_,n,hs,_⟩ := hz
    left; right; left
    refine ⟨n+3,?_⟩
    rw [←hS,Int.pow_add]
    exact_mod_cast hs
  · obtain ⟨_,_,n,hs,_⟩ := hone
    left; right; right
    refine ⟨n+4,?_⟩
    rw [show (encode x y).l+(encode x y).h=(x:Int)+y+1 by omega,Int.pow_add]
    exact_mod_cast hs
  · obtain ⟨_,_,hpar,n,hs,hm⟩ := he
    right
    refine ⟨n+2,by omega,affine_of_equations a k x y (n+2) (by omega) (by omega) ?_⟩
    rw [show n+2=(n+1)+1 by omega,Nat.pow_succ,hpar,Nat.add_zero]
    rw [Nat.mul_comm (2^(n+1)) 2,Nat.mul_assoc,←hs]
    omega
  · obtain ⟨_,_,hpar,n,hs,hm⟩ := ho
    right
    refine ⟨n+2,by omega,affine_of_equations a k x y (n+2) (by omega) (by omega) ?_⟩
    rw [show n+2=(n+1)+1 by omega,Nat.pow_succ,hpar]
    rw [show a+2+1=a+3 by omega,Nat.mul_comm (2^(n+1)) 2,Nat.mul_assoc,←hs]
    omega

/-- Soundness for the exact original section map. -/
theorem source_sieve_sound (b : Nat) (P : Coord → Prop) (root : P (reduce b (encode 5 1)))
    (birth : ∀ s, BirthResidue b s → P (reduce b s))
    (closed : ∀ r s, 1≤r → r<b → P (reduce b s) → P (reduce b (affine r (reduce b s))))
    (s : Nat × Nat) (hs : Reach secNext s) : P (reduce b (encode s.1 s.2)) :=
  sieve_sound secNext source_edge_contract b P root birth closed s hs

#print axioms source_edge_contract
#print axioms source_sieve_sound
end BB6.Agent12Dyadic
