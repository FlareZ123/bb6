import CapSieveLift
namespace CapSieve

/-- The exact 3-adic period increment, including its nonzero leading digit. -/
theorem pow_period_exact (t : Nat) :
    ∃ k : Nat, 2^(2*3^t)=1+3^(t+1)*k ∧ k%3=1 := by
  induction t with
  | zero => exact ⟨1,by decide,by decide⟩
  | succ t ih =>
    obtain ⟨k,hk,hu⟩ := ih
    refine ⟨k+3*3^t*k*k+3*3^t*3^t*k*k*k,?_,?_⟩
    · rw [show 2*3^(t+1)=(2*3^t)*3 by rw [Nat.pow_succ,Nat.mul_assoc],Nat.pow_mul,hk]
      simp only [Nat.pow_succ (n:=3)]
      grind
    · simp [Nat.add_mod,Nat.mul_mod,hu]

/-- A unit coefficient permutes all three residue digits. -/
theorem unit_digit_unique (q b : Int) (hu : b%3≠0) :
    ∃ l : Nat, l<3 ∧ (q+b*l)%3=0 ∧
      ∀ k : Nat, k<3 → (q+b*k)%3=0 → k=l := by
  have h (l : Nat) : (q+b*l)%3=(q%3+(b%3)*(l:Int))%3 := by
    rw [Int.add_emod,Int.mul_emod]; simp [Int.add_emod,Int.mul_emod]
  have hb : b%3=1 ∨ b%3=2 := by omega
  have hq : q%3=0 ∨ q%3=1 ∨ q%3=2 := by omega
  rcases hb with hb|hb <;> rcases hq with hq|hq|hq
  all_goals first
    | refine ⟨0,by decide,?_,?_⟩ <;> simp [h,hb,hq] <;> omega
    | refine ⟨1,by decide,?_,?_⟩ <;> simp [h,hb,hq] <;> omega
    | refine ⟨2,by decide,?_,?_⟩ <;> simp [h,hb,hq] <;> omega

/-- Multiplicative lifting of an exponential-affine numerator. Each unit
    numerator has a unique integral lift to the next power of three. -/
theorem exp_unit_lift (t : Nat) (A C p : Int) (hu : (A*p)%3≠0)
    (hd : (3^(t+1):Int)∣(A*p+C)) :
    ∃ l : Nat, l<3 ∧
      (A*p*(2^(2*3^t):Int)^l+C)%(3^(t+2):Int)=0 ∧
      ∀ k : Nat, k<3 → (A*p*(2^(2*3^t):Int)^k+C)%(3^(t+2):Int)=0 → k=l := by
  obtain ⟨v,hv,hvu⟩ := pow_period_exact t
  have hv' : (2^(2*3^t):Int)=1+(3^(t+1):Int)*v := by exact_mod_cast hv
  obtain ⟨q,hq⟩ := hd
  let D : Int := 3^(t+1)
  have hD : 0<D := Int.pow_pos (by decide)
  have hD3 : D%3=0 := by simp [D,Int.pow_succ]
  have hb : (A*p*(v:Int))%3≠0 := by
    have h : (v:Int)%3=1 := by exact_mod_cast hvu
    rw [Int.mul_emod,h]; simpa using hu
  obtain ⟨l,hl,hlz,hluniq⟩ := unit_digit_unique q (A*p*v) hb
  have equiv (k : Nat) (hk : k<3) :
      (A*p*(2^(2*3^t):Int)^k+C)%(3^(t+2):Int)=0 ↔ (q+A*p*v*k)%3=0 := by
    have hq' : A*p+C=D*q := hq
    have hv'' : (2^(2*3^t):Int)=1+D*v := hv'
    have hpow : (3^(t+2):Int)=3*D := by simp [D,Int.pow_succ,Int.mul_comm]
    have hdv : ∃ u : Int, D=3*u := by exact ⟨D/3,by omega⟩
    obtain ⟨u,hu'⟩ := hdv
    have he : ∃ z : Int, A*p*(1+D*v)^k+C=D*(q+A*p*v*k)+(3*D)*z := by
      have hk' : k=0 ∨ k=1 ∨ k=2 := by omega
      rcases hk' with rfl|rfl|rfl
      · exact ⟨0,by simpa using hq'⟩
      · refine ⟨0,?_⟩; simp; grind
      · refine ⟨A*p*u*v*v,?_⟩; simp [Int.pow_succ]; grind
    obtain ⟨z,hz⟩ := he
    rw [hv'',hpow,hz,Int.add_mul_emod_self_left,Int.mul_comm 3 D,Int.mul_emod_mul_of_pos _ _ hD]
    constructor
    · intro h; exact (Int.mul_eq_zero.mp h).resolve_left (by omega)
    · intro h; rw [h,Int.mul_zero]
  exact ⟨l,hl,(equiv l hl).mpr hlz,fun k hk h=>hluniq k hk ((equiv k hk).mp h)⟩

#print axioms pow_period_exact
#print axioms unit_digit_unique
#print axioms exp_unit_lift
end CapSieve
