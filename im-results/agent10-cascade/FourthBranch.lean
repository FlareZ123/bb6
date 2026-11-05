import FourEven
set_option maxHeartbeats 0
set_option maxRecDepth 8192
namespace CascadeAgent10FourthBranch
open CascadeResetInverse CascadeUniformFatal CascadeAgent10Four

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

theorem band_growth (n:Nat) (hn:10≤n) :
    8*(31*n+49) ≤ 5*2^n := by
  have h : ∀ k:Nat, 8*(31*(k+10)+49) ≤ 5*2^(k+10) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show k+1+10=k+10+1 by omega,Nat.pow_succ]
      omega
  have he:n=(n-10)+10 := by omega
  rw [he]
  exact h (n-10)

theorem fifth_growth (n:Nat) (hn:10≤n) :
    63*n+97 ≤ 2^n := by
  have h : ∀ k:Nat, 63*(k+10)+97 ≤ 2^(k+10) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show k+1+10=k+10+1 by omega,Nat.pow_succ]
      omega
  have he:n=(n-10)+10 := by omega
  rw [he]
  exact h (n-10)

/-- Precisely at the fourth inverse ancestor of #746's surviving fatal
    classes, the next odd-predecessor gate is open modulo nine. -/
theorem fourth_divnine (n:Nat) (hn:10≤n)
    (hres:n%18=10 ∨ n%18=17) :
    (2*fourthPred n+5)%9=0 := by
  have hb := fifth_growth n hn
  have hr:fourthPred n+31*n+49=4*2^n := by
    dsimp [fourthPred]
    omega
  have hp := pow_mod_six n
  rcases hres with h|h
  · have hm:n%6=4 := by omega
    have hm9:2^n%9=7 := by rw [hp,hm]
    omega
  · have hm:n%6=5 := by omega
    have hm9:2^n%9=5 := by rw [hp,hm]
    omega

def d (n:Nat) := (2*fourthPred n+5)/9
def oddPre (n:Nat) :=
  4*d n-8*2^(n-2)-(n-2)-5
def evenPre (n:Nat) := 4*2^n-63*n-97

theorem odd_factor (n:Nat) (hn:10≤n)
    (hres:n%18=10 ∨ n%18=17) :
    9*d n=2*fourthPred n+5 ∧ (d n)%2=1 := by
  have hmod := fourth_divnine n hn hres
  have hd := Nat.mod_add_div (2*fourthPred n+5) 9
  have heq:9*d n=2*fourthPred n+5 := by
    dsimp [d]
    omega
  constructor
  · exact heq
  · omega

theorem odd_band (n:Nat) (hn:10≤n)
    (hres:n%18=10 ∨ n%18=17) :
    6*2^(n-2)+1 ≤ 2*d n ∧ 2*d n ≤ 8*2^(n-2)-1 := by
  have hg := band_growth n hn
  have hb := fifth_growth n hn
  have hf := odd_factor n hn hres
  have hp : 2^n=4*2^(n-2) := by
    have he : 2^n=2^((n-2)+2) := congrArg (fun m : Nat => 2^m) (by omega)
    rw [Nat.pow_add] at he
    omega
  have hu: fourthPred n + 31*n+49=4*2^n := by
    dsimp [fourthPred]
    omega
  omega

/-- The first strictly odd inverse branch exists uniformly for each
    index n≡10,17 mod18 once the four forced even ancestors are removed. -/
theorem fourth_odd_parent (n:Nat) (hn:10≤n)
    (hres:n%18=10 ∨ n%18=17) :
    ResetParent (oddPre n) (fourthPred n) := by
  have hf := odd_factor n hn hres
  have hb := odd_band n hn hres
  have hg := band_growth n hn
  have hp : 2^n=4*2^(n-2) := by
    have he : 2^n=2^((n-2)+2) := congrArg (fun m : Nat => 2^m) (by omega)
    rw [Nat.pow_add] at he
    omega
  have heq : 2*(2*d n)=8*2^(n-2)+oddPre n+(n-2)+5 := by
    dsimp [oddPre]
    omega
  have hprod : 2*fourthPred n+5=3^(1+1)*d n := by
    have : 3^(1+1)=9 := by decide
    rw [this]
    omega
  exact Or.inr ⟨n-2,1,d n,hf.2,hb,hprod,heq⟩

/-- The dyadic inverse arm survives at the same fork, independently. -/
theorem fourth_even_parent (n:Nat) (hn:10≤n) :
    ResetParent (evenPre n) (fourthPred n) := by
  have hb := fifth_growth n hn
  have hp : 2^n=2*2^(n-1) := by
    have he : 2^n=2^((n-1)+1) := congrArg (fun m : Nat => 2^m) (by omega)
    rw [Nat.pow_succ] at he
    omega
  have hlow : 6*2^(n-1)-1 ≤ fourthPred n := by
    dsimp [fourthPred]
    rw [hp]
    omega
  have hhigh : fourthPred n ≤ 8*2^(n-1)-3 := by
    dsimp [fourthPred]
    rw [hp]
    omega
  have heq : 2*fourthPred n =8*2^(n-1)+evenPre n+(n-1) := by
    dsimp [fourthPred,evenPre]
    rw [hp]
    omega
  exact Or.inl ⟨n-1,⟨hlow,hhigh⟩,heq⟩

/-- The fifth inverse level genuinely forks into two different exact
    first-reset parents, proving the four-even-level simplification sharp. -/
theorem fourth_has_distinct_parents (n:Nat) (hn:10≤n)
    (hres:n%18=10 ∨ n%18=17) :
    ∃ x y, x≠y ∧ ResetParent x (fourthPred n) ∧
      ResetParent y (fourthPred n) := by
  have ho := fourth_odd_parent n hn hres
  have he := fourth_even_parent n hn
  have hb := odd_band n hn hres
  have hg := fifth_growth n hn
  have hlt : oddPre n < 2*2^n := by
    dsimp [oddPre]
    have hp : 2^n=4*2^(n-2) := by
      have he : 2^n=2^((n-2)+2) := congrArg (fun m : Nat => 2^m) (by omega)
      rw [Nat.pow_add] at he
      omega
    omega
  have hge : 3*2^n ≤ evenPre n := by
    dsimp [evenPre]
    omega
  refine ⟨oddPre n, evenPre n, ?_,ho,he⟩
  omega

#print axioms fourth_odd_parent
#print axioms fourth_even_parent
#print axioms fourth_has_distinct_parents
end CascadeAgent10FourthBranch
