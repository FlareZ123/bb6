import SheepEvenReachInverse

namespace Sheep138ChildHighH

/-- The first rational child has no high h congruence. -/
theorem child1_root_nonresidue (k : Nat) :
    2^(141+4860*k)%1215 ≠ 17 := by
  have hp : 2^324%1215=1 := by decide
  have he : 141+4860*k=141+324*(15*k) := by omega
  have hp2 : (2^324)^(15*k)%1215=1 := by
    rw [Nat.pow_mod (2^324) (15*k) 1215, hp]
    simp
  rw [he, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, hp2]
  decide

/-- The second rational child has no high h congruence. -/
theorem child2_root_nonresidue (k : Nat) :
    2^(143+4860*k)%729 ≠ 149 := by
  have hp : 2^486%729=1 := by decide
  have he : 143+4860*k=143+486*(10*k) := by omega
  have hp2 : (2^486)^(10*k)%729=1 := by
    rw [Nat.pow_mod (2^486) (10*k) 729, hp]
    simp
  rw [he, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, hp2]
  decide

/-- All possible first-even predecessors of the child
15*y+2=2^(141+4860k) must have h in 0..3. -/
theorem child1_h_lt_four (k y h u : Nat)
    (hy : 15*y+2=2^(141+4860*k))
    (hout : y=1+3^h*u) : h<4 := by
  by_cases hlt : h<4
  · exact hlt
  have hge : 4≤h := by omega
  obtain ⟨t,ht⟩ : ∃ t, h=4+t := ⟨h-4,by omega⟩
  have hp3 : 3^h=81*3^t := by
    rw [ht,Nat.pow_add]
  rw [hp3] at hout
  have he : 2^(141+4860*k)=17+1215*(3^t*u) := by
    have hm : 15*(81*3^t*u)=1215*(3^t*u) := by
      calc
        15*(81*3^t*u) = (15*81)*(3^t*u) := by ac_rfl
        _ = 1215*(3^t*u) := by rfl
    rw [←hy,hout,Nat.mul_add,hm]
    omega
  have hmod : 2^(141+4860*k)%1215=17 := by
    rw [he,Nat.add_mod]
    have hm : (1215*(3^t*u))%1215=0 := by simp
    rw [hm]
  exact False.elim (child1_root_nonresidue k hmod)

/-- All possible first-even predecessors of the child
81*y+68=2^(143+4860k) must have h in 0..1. -/
theorem child2_h_lt_two (k y h u : Nat)
    (hy : 81*y+68=2^(143+4860*k))
    (hout : y=1+3^h*u) : h<2 := by
  by_cases hlt : h<2
  · exact hlt
  have hge : 2≤h := by omega
  obtain ⟨t,ht⟩ : ∃ t, h=2+t := ⟨h-2,by omega⟩
  have hp3 : 3^h=9*3^t := by
    rw [ht,Nat.pow_add]
  rw [hp3] at hout
  have he : 2^(143+4860*k)=149+729*(3^t*u) := by
    have hm : 81*(9*3^t*u)=729*(3^t*u) := by
      calc
        81*(9*3^t*u) = (81*9)*(3^t*u) := by ac_rfl
        _ = 729*(3^t*u) := by rfl
    rw [←hy,hout,Nat.mul_add,hm]
    omega
  have hmod : 2^(143+4860*k)%729=149 := by
    rw [he,Nat.add_mod]
    have hm : (729*(3^t*u))%729=0 := by simp
    rw [hm]
  exact False.elim (child2_root_nonresidue k hmod)

#print axioms child1_h_lt_four
#print axioms child2_h_lt_two
end Sheep138ChildHighH
