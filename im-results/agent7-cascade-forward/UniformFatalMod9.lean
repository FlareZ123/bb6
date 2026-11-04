import UniformFatalParent

namespace CascadeUniformFatal
open CascadeResetInverse CascadeManyShield

private theorem mod9_pow_lower (n : Nat) (hn : 2 ≤ n) : n+2 ≤ 2^n := by
  have h : ∀ m : Nat, m+4 ≤ 2^(m+2) := by
    intro m
    induction m with
    | zero => decide
    | succ m ih =>
        rw [show m+1+2=(m+2)+1 by omega, Nat.pow_succ]
        omega
  have hh := h (n-2)
  have he : n-2+2=n := by omega
  rw [he] at hh
  omega

private theorem pow_period_six (n : Nat) : 2^(n+6)%9 = 2^n%9 := by
  rw [Nat.pow_add]
  simp [Nat.mul_mod]

private theorem pow_mod_six (n : Nat) : 2^n%9 = 2^(n%6)%9 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n < 6
    · simp [Nat.mod_eq_of_lt hn]
    · have hm : n-6<n := by omega
      have he : n=(n-6)+6 := by omega
      have hmod : n%6=(n-6)%6 := by omega
      rw [he,pow_period_six]
      rw [ih (n-6) hm]
      have hemod : ((n-6)+6)%6=(n-6)%6 := by omega
      rw [hemod]

/-- Two thirds of the surviving fatal residue classes have exactly
    one factor of three in 2*fatal(n)+5. In particular it is not
    divisible by 9, uniformly for every n in these classes. -/
theorem fatal_not_div9 (n : Nat) (hn : 4 ≤ n)
    (hres : n%18=10 ∨ n%18=11 ∨ n%18=16 ∨ n%18=17) :
    (2*fatal n+5)%9 ≠ 0 := by
  have hp : n+2 ≤ 2^n := mod9_pow_lower n (by omega)
  have hf : 2*fatal n+5 + 2*n+3 = 8*2^n := by
    dsimp [fatal]
    omega
  have hperiod := pow_mod_six n
  rcases hres with h | h | h | h
  · have hm6 : n%6 = 4 := by omega
    have hm9 : (2^n)%9 = 7 := by rw [hperiod,hm6]
    omega
  · have hm6 : n%6 = 5 := by omega
    have hm9 : (2^n)%9 = 5 := by rw [hperiod,hm6]
    omega
  · have hm6 : n%6 = 4 := by omega
    have hm9 : (2^n)%9 = 7 := by rw [hperiod,hm6]
    omega
  · have hm6 : n%6 = 5 := by omega
    have hm9 : (2^n)%9 = 5 := by rw [hperiod,hm6]
    omega

/-- Uniform complete first-reset parent uniqueness in four residue classes.
    All n%18=10,11,16,17 have the same single source first-reset parent
    4*2^n-3*n-7; every other possible predecessor requires a divisible-by-9
    odd arm, which the congruence above excludes. -/
theorem fatal_only_even_parent (h n : Nat) (hn : 4 ≤ n)
    (hres : n%18=10 ∨ n%18=11 ∨ n%18=16 ∨ n%18=17)
    (hp : ResetParent h (fatal n)) :
    h = 4*2^n-3*n-7 := by
  rcases fatal_parent_normal_form h n hn hp with he | ⟨k,t,d,ht,hodd,hband,heq,hq⟩
  · exact he
  · have hh : t+1 = 2+(t-1) := by omega
    have hpow : 3^(t+1)%9=0 := by
      rw [hh,Nat.pow_add]
      simp
    have hd : (2*fatal n+5)%9=0 := by
      rw [heq,Nat.mul_mod,hpow]
      simp
    exact False.elim ((fatal_not_div9 n hn hres) hd)

#print axioms fatal_not_div9
#print axioms fatal_only_even_parent
end CascadeUniformFatal
