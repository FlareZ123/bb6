import Std
namespace Sheep648ParentIdentity

/-- The sole surviving root generic predecessor has the exact child affine identity,
for all k and without a bounded orbit simulation. -/
theorem root_generic_to_child (k x v u : Nat)
    (hx : x=2^2*v)
    (hF : 2*(1+2^5*u)+1=(2^(2+1)+1)*v+2*2)
    (hY : 2^(648+122472*k)=1+3^5*u) :
    2187*x+1228=2^(656+122472*k) := by
  have hp : 2^(656+122472*k)=256*2^(648+122472*k) := by
    calc
      2^(656+122472*k) = 2^8*2^(648+122472*k) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      _ = 256*2^(648+122472*k) := by simp [show (2^8:Nat)=256 by decide]
  have h1 : x=4*v := by simpa using hx
  have hf : 2*(1+32*u)+1=9*v+4 := by simpa using hF
  have h2 : 3+64*u=9*v+4 := by omega
  have h3 : 2^(648+122472*k)=1+243*u := by simpa using hY
  rw [hp,h1,h3]
  omega

#print axioms root_generic_to_child
end Sheep648ParentIdentity
