import Std

namespace NeedleCongruence

/-- Extended Euclidean identity over natural inputs, with signed coefficients. -/
theorem bezout (a b : Nat) : ∃ x y : Int, (a:Int)*x+(b:Int)*y=(a.gcd b:Int) := by
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    by_cases hb : b=0
    · subst b; exact ⟨1,0,by simp⟩
    have hpos : 0<b := Nat.pos_of_ne_zero hb
    obtain ⟨x,y,hxy⟩ := ih (a%b) (Nat.mod_lt a hpos) b
    refine ⟨y,x-(a/b:Nat)*y,?_⟩
    have he : (a%b:Nat) + b*(a/b)=a := Nat.mod_add_div a b
    have heI : (a%b:Nat)+(b:Int)*(a/b:Nat)=(a:Int) := by exact_mod_cast he
    have hg : b.gcd (a%b)=a.gcd b := by rw [Nat.gcd_comm b (a%b),←Nat.gcd_rec b a,Nat.gcd_comm]
    rw [hg] at hxy
    grind

/-- Solve one linear congruence whenever the gcd obstruction vanishes,
with an arbitrarily large nonnegative solution. -/
theorem linear_solve (A M : Nat) (B R : Int) (N : Nat) (hM : 0<M)
    (h : (A.gcd M:Int) ∣ R-B) :
    ∃ q : Nat, N≤q ∧ (M:Int) ∣ (A:Int)*(q:Int)+B-R := by
  obtain ⟨x,y,hxy⟩ := bezout A M
  obtain ⟨z,hz⟩ := h
  let u : Int := x*z
  let t : Int := u % M
  have ht : 0≤t := Int.emod_nonneg _ (by omega)
  let q : Nat := t.toNat+M*N
  have hq : (q:Int)=t+(M:Int)*(N:Int) := by simp [q,Int.toNat_of_nonneg ht]
  have hdiv : t+(M:Int)*(u/M)=u := Int.emod_add_mul_ediv u M
  refine ⟨q,?_,?_⟩
  · have hn : N≤M*N := by
      have hh := Nat.mul_le_mul_right N (show 1≤M by omega)
      simpa using hh
    omega
  · refine ⟨(A:Int)*((N:Int)-u/M)-y*z,?_⟩
    rw [hq]
    dsimp [u] at hdiv ⊢
    grind

theorem coprime_solve (A M : Nat) (B R : Int) (N : Nat) (hM : 0<M)
    (h : A.Coprime M) :
    ∃ q : Nat, N≤q ∧ (M:Int) ∣ (A:Int)*(q:Int)+B-R := by
  apply linear_solve A M B R N hM
  simp [h.gcd_eq_one]

/-- Coprime moduli can be combined with arbitrary lower bound. -/
theorem crt (M P : Nat) (a b : Int) (N : Nat) (hM : 0<M) (hP : 0<P)
    (h : M.Coprime P) : ∃ q : Nat, N≤q ∧ (M:Int) ∣ (q:Int)-a ∧ (P:Int) ∣ (q:Int)-b := by
  let r : Int := a % M
  have hr : 0≤r := Int.emod_nonneg _ (by omega)
  obtain ⟨u,hu,hdiv⟩ := coprime_solve M P r b N hP h
  let q := r.toNat+M*u
  have hq : (q:Int)=r+(M:Int)*(u:Int) := by simp [q,Int.toNat_of_nonneg hr]
  refine ⟨q,?_,?_,?_⟩
  · have hh : u≤M*u := by
      have hh := Nat.mul_le_mul_right u (show 1≤M by omega)
      simpa using hh
    omega
  · refine ⟨(u:Int)-a/M,?_⟩
    rw [hq]
    have he := Int.emod_add_mul_ediv a M
    dsimp [r]
    grind
  · rw [hq]
    simpa [Int.add_comm r] using hdiv

/-- Any odd number is coprime to any power of two. -/
theorem odd_coprime_pow (M h : Nat) (hodd : M%2=1) : M.Coprime (2^h) := by
  have hh : M.Coprime 2 := by
    unfold Nat.Coprime
    rw [Nat.gcd_comm,Nat.gcd_rec,hodd]
    decide
  exact hh.pow_right h

#print axioms bezout
#print axioms linear_solve
#print axioms crt
end NeedleCongruence
