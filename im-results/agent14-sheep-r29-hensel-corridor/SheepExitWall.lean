import Std

namespace SheepExitWall

/-- A source-equation obstruction at any depth of the distinguished
    h=0,a=2 inverse Sheep chain, independent of the target exponent. -/
theorem no_generic_exit
    {q a v n x y : Nat}
    (hq : Nat.Coprime q 2)
    (hchain : 9^n*(x+12)=8^n*(y+12))
    (hbase : ¬ q ∣ y+12)
    (hmod : q ∣ 2^(a+1)+1)
    (haval : q ∣ 2*a+23)
    (hgeneric : 2*x+1 = (2^(a+1)+1)*v+2*a) : False := by
  have hprod : q ∣ (2^(a+1)+1)*v := by
    obtain ⟨w, hw⟩ := hmod
    refine ⟨w*v, ?_⟩
    rw [hw]
    ac_rfl
  have hsum : q ∣ (2^(a+1)+1)*v+(2*a+23) :=
    Nat.dvd_add hprod haval
  have heq : 2*(x+12) = (2^(a+1)+1)*v+(2*a+23) := by
    omega
  have htwo : q ∣ 2*(x+12) := heq ▸ hsum
  have hx : q ∣ x+12 := hq.dvd_of_dvd_mul_left htwo
  have hfrom : q ∣ 9^n*(x+12) := by
    obtain ⟨w, hw⟩ := hx
    refine ⟨9^n*w, ?_⟩
    rw [hw]
    ac_rfl
  have hto : q ∣ 8^n*(y+12) := hchain ▸ hfrom
  have h8 : Nat.Coprime q 8 := by
    simpa using (hq.pow_right 3)
  exact hbase ((h8.pow_right n).dvd_of_dvd_mul_left hto)

#print axioms no_generic_exit
end SheepExitWall
