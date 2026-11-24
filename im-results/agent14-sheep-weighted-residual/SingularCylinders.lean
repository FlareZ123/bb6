import GenericResidual

namespace SheepWeightedResidual

/-- Exact source cylinder for the first zero-residual branch. -/
theorem singular_type1_cylinder (u v up : Nat)
    (hu : u%2=1) (hv : v%2=1) (hup : up%2=1)
    (hstep : 4*v+3=5*u+2) (hout : 4*up=1+3*v) :
    ∃ k, u=1+32*k ∧ up=1+30*k := by
  have hv8 : v%8=1 := by omega
  have hu32 : u%32=1 := by omega
  let k := u/32
  have huform : u=1+32*k := by
    dsimp [k]
    omega
  have hvform : v=1+40*k := by
    rw [huform] at hstep
    omega
  have hupform : up=1+30*k := by
    rw [hvform] at hout
    omega
  exact ⟨k,huform,hupform⟩

/-- Exact source cylinder for the second zero-residual branch. -/
theorem singular_type3_cylinder (u v up : Nat)
    (hu : u%2=1) (hv : v%2=1) (hup : up%2=1)
    (hstep : 4*v+3=17*u+6) (hout : 16*up=1+3*v) :
    ∃ k, u=1+128*k ∧ up=1+102*k := by
  have hv32 : v%32=5 := by omega
  have hu128 : u%128=1 := by omega
  let k := u/128
  have huform : u=1+128*k := by
    dsimp [k]
    omega
  have hvform : v=5+544*k := by
    rw [huform] at hstep
    omega
  have hupform : up=1+102*k := by
    rw [hvform] at hout
    omega
  exact ⟨k,huform,hupform⟩

/-- The next first-step excess after a type-1 singular edge. -/
theorem singular_type1_next_excess (k : Nat) :
    (2^(2+1)+1)*(1+30*k)+2*2-3 = 2*(5+135*k) := by
  simp [Nat.pow_succ]
  omega

/-- The next first-step excess after a type-3 singular edge. -/
theorem singular_type3_next_excess (k : Nat) :
    (2^(4+1)+1)*(1+102*k)+2*4-3 = 2*(19+1683*k) := by
  simp [Nat.pow_succ]
  omega

/-- Any immediate terminal successor of a type-1 singular edge obeys this equation. -/
theorem singular_type1_terminal_equation
    (k H B w : Nat)
    (hdiv : 2^H*w=5+135*k)
    (hhalt : 2^B=1+3^H*w) :
    2^H*(2^B-1)=3^H*(5+135*k) := by
  calc
    2^H*(2^B-1) = 2^H*(3^H*w) := by rw [hhalt]; congr 1 <;> omega
    _ = 3^H*(2^H*w) := by ac_rfl
    _ = 3^H*(5+135*k) := by rw [hdiv]

/-- Any immediate terminal successor of a type-3 singular edge obeys this equation. -/
theorem singular_type3_terminal_equation
    (k H B w : Nat)
    (hdiv : 2^H*w=19+1683*k)
    (hhalt : 2^B=1+3^H*w) :
    2^H*(2^B-1)=3^H*(19+1683*k) := by
  calc
    2^H*(2^B-1) = 2^H*(3^H*w) := by rw [hhalt]; congr 1 <;> omega
    _ = 3^H*(2^H*w) := by ac_rfl
    _ = 3^H*(19+1683*k) := by rw [hdiv]

#print axioms singular_type1_cylinder
#print axioms singular_type3_cylinder
#print axioms singular_type1_next_excess
#print axioms singular_type3_next_excess
#print axioms singular_type1_terminal_equation
#print axioms singular_type3_terminal_equation

end SheepWeightedResidual
