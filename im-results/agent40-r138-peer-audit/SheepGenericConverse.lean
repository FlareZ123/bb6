import EvenEdge
import SheepEvenInverseAlgebra

namespace SheepGenericConverse

/-- An algebraic generic even-edge witness is an actual source-level first-even
section return, with full Sheep.Step semantics and exact odd-run compression. -/
theorem generic_to_source {x y : Nat}
    (hg : SheepEvenInverseAlgebra.GenericEdge x y) :
    SheepEven.EvenEdge x y := by
  obtain ⟨a,h,v,u,ha,hv,hodd,hu,hx,hformula,hy⟩ := hg
  have hpow : 2^(a+1)=2*2^a := by
    rw [Nat.pow_succ]
    omega
  have hhalf : 2*((v-1)/2)+1=v := by omega
  have hlin :
      2*(1+2^h*u)+1=2*(2^a*v)+v+2*a := by
    rw [hpow] at hformula
    calc
      2*(1+2^h*u)+1=(2*2^a+1)*v+2*a := hformula
      _ = 2*(2^a*v)+v+2*a := by simp [Nat.add_mul, Nat.mul_assoc]
  have hz : 2^a*v+a+(v-1)/2 = 1+2^h*u := by omega
  have hs : SheepEven.Step (2^a*v) (1+2^h*u) := by
    rw [←hz]
    exact SheepEven.Step.generic a v hodd hv
  have hz5 : 5≤1+2^h*u := by
    have hpos : 0<2^a := Nat.pow_pos (by decide)
    have hmul := Nat.mul_le_mul_right v (show 1 ≤ 2^a by omega)
    have hlo : 5 ≤ 2^a*v := by omega
    have hinc := SheepEven.step_increases hs
    omega
  refine ⟨1+2^h*u,h,u,?_,hz5,hu,rfl,hy⟩
  rw [hx]
  exact hs

#print axioms generic_to_source
end SheepGenericConverse
