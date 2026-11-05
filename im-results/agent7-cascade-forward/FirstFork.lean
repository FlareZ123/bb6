import SecondEven

namespace CascadeFirstFork
open CascadeResetInverse CascadeUniformFatal CascadeManyShield CascadeSweep

/-- The exact odd first-reset predecessor with valuation exponent one. -/
def oddPre (n u : Nat) : Nat :=
  4*((2*u+5)/9)-8*2^(n-2)-(n-2)-5

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
      rw [he,pow_period_six]
      rw [ih (n-6) hm]
      have hemod : ((n-6)+6)%6=(n-6)%6 := by omega
      rw [hemod]

private theorem pow_at_least_16 (n : Nat) (hn : 4 ≤ n) : 16 ≤ 2^n := by
  have hp : 2^4 ≤ 2^n := Nat.pow_le_pow_right (by decide) hn
  exact hp

/-- A source-first-reset odd parent exists for a near-top target whose
    odd-output parameter is divisible by nine. -/
theorem odd_parent_near_top (n u A : Nat) (hn : 4 ≤ n)
    (hclose : u+A=4*2^n)
    (hsize : 8*A ≤ 5*2^n)
    (hdiv : (2*u+5)%9=0) :
    ResetParent (oddPre n u) u := by
  let d := (2*u+5)/9
  let p := 2^(n-2)
  have hd : 9*d=2*u+5 := by
    have hmod := Nat.mod_add_div (2*u+5) 9
    dsimp [d]
    omega
  have hodd : d%2=1 := by omega
  have hpow : 2^n=4*p := by
    have he : 2^n=2^((n-2)+2) := congrArg (fun m : Nat => 2^m) (by omega)
    rw [Nat.pow_add] at he
    dsimp [p]
    omega
  have hlarge : 4 ≤ p := by
    have hp := pow_at_least_16 n hn
    omega
  have hbandlo : 6*p+1 ≤ 2*d := by omega
  have hbandhi : 2*d ≤ 8*p-1 := by omega
  have hlinear : n+3 ≤ 4*p := by
    have hp := n_plus_three_le_pow n hn
    omega
  have hrelation : 2*(2*d) = 8*p+oddPre n u+(n-2)+5 := by
    dsimp [oddPre, d, p]
    omega
  have hfactor : 2*u+5=3^(1+1)*d := by
    have hp : 3^(1+1)=9 := by decide
    rw [hp]
    omega
  exact Or.inr ⟨n-2,1,d,hodd,⟨hbandlo,hbandhi⟩,
    hfactor,hrelation⟩

private theorem fatal_close (n:Nat) (hn:4≤n) :
    fatal n+(n+4)=4*2^n := by
  have hp := n_plus_three_le_pow n hn
  dsimp [fatal]
  omega

private theorem fatal_size (n:Nat) (hn:4≤n) :
    8*(n+4) ≤ 5*2^n := by
  have h : ∀ k:Nat, 8*((k+4)+4) ≤ 5*2^(k+4) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show k+1+4=k+4+1 by omega,Nat.pow_succ]
      omega
  have he : n=(n-4)+4 := by omega
  rw [he]
  exact h (n-4)

/-- For every n≡4 or 5 (mod 18), a real odd first-reset parent exists
    at the fatal height. This does not imply blank-root reachability. -/
theorem fatal_divnine (n:Nat) (hn:4≤n)
    (hres:n%18=4 ∨ n%18=5) :
    (2*fatal n+5)%9=0 := by
  have hf := fatal_close n hn
  have hp := pow_mod_six n
  rcases hres with h|h
  · have hm:n%6=4 := by omega
    have hm9:2^n%9=7 := by rw [hp,hm]
    omega
  · have hm:n%6=5 := by omega
    have hm9:2^n%9=5 := by rw [hp,hm]
    omega

theorem fatal_has_odd_parent (n:Nat) (hn:4≤n)
    (hres:n%18=4 ∨ n%18=5) :
    ResetParent (oddPre n (fatal n)) (fatal n) :=
  odd_parent_near_top n (fatal n) (n+4) hn
    (fatal_close n hn) (fatal_size n hn) (fatal_divnine n hn hres)

private theorem second_size (n:Nat) (hn:10≤n) :
    8*(7*n+13) ≤ 5*2^n := by
  have h : ∀ k:Nat, 8*(7*(k+10)+13) ≤ 5*2^(k+10) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show k+1+10=k+10+1 by omega,Nat.pow_succ]
      omega
  have he : n=(n-10)+10 := by omega
  rw [he]
  exact h (n-10)

private theorem second_close (n:Nat) (hn:10≤n) :
    secondPred n+(7*n+13)=4*2^n := by
  have hsize := second_size n hn
  have hp : 7*n+13 ≤ 2^n := by omega
  dsimp [secondPred]
  omega

/-- For n≡11 or 16 (mod18), the second forced even predecessor opens
    a genuine odd t=1 first-reset branch. -/
theorem second_divnine (n:Nat) (hn:10≤n)
    (hres:n%18=11 ∨ n%18=16) :
    (2*secondPred n+5)%9=0 := by
  have hf := second_close n hn
  have hp := pow_mod_six n
  rcases hres with h|h
  · have hm:n%6=5 := by omega
    have hm9:2^n%9=5 := by rw [hp,hm]
    omega
  · have hm:n%6=4 := by omega
    have hm9:2^n%9=7 := by rw [hp,hm]
    omega

theorem second_has_odd_parent (n:Nat) (hn:10≤n)
    (hres:n%18=11 ∨ n%18=16) :
    ResetParent (oddPre n (secondPred n)) (secondPred n) :=
  odd_parent_near_top n (secondPred n) (7*n+13) (by omega)
    (second_close n hn) (second_size n hn) (second_divnine n hn hres)

#print axioms odd_parent_near_top

#print axioms fatal_has_odd_parent
#print axioms second_has_odd_parent
end CascadeFirstFork
