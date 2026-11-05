import FourthOddGap
set_option maxHeartbeats 0
namespace CascadeAgent10Mod81
open CascadeAgent10Four CascadeAgent10FourthBranch

private theorem pow_period_fiftyfour (n : Nat) : 2^(n+54)%81 = 2^n%81 := by
  rw [Nat.pow_add]
  simp [Nat.mul_mod]

theorem pow_mod_fiftyfour (n : Nat) : 2^n%81 = 2^(n%54)%81 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n < 54
    · simp [Nat.mod_eq_of_lt hn]
    · have hm : n-54<n := by omega
      have he : n=(n-54)+54 := by omega
      rw [he,pow_period_fiftyfour]
      rw [ih (n-54) hm]
      have hemod : ((n-54)+54)%54=(n-54)%54 := by omega
      rw [hemod]

/-- The two v3>=3 mod54 sectors have exactly v3=3 in four of their
    six mod162 subcases. -/
theorem fourth_not_div81 (n:Nat) (hn:10≤n)
    (hres:n%162=10 ∨ n%162=53 ∨ n%162=118 ∨ n%162=161) :
    (2*fourthPred n+5)%81≠0 := by
  have hbound : 31*n+49≤2^n:=by
    have h : ∀ k:Nat,31*(k+10)+49≤2^(k+10):=by
      intro k
      induction k with
      | zero => decide
      | succ k ih =>
        rw [show k+1+10=k+10+1 by omega,Nat.pow_succ]
        omega
    have he:n=(n-10)+10:=by omega
    rw [he]
    exact h (n-10)
  have heq : 2*fourthPred n+5+62*n+93=8*2^n:=by
    dsimp [fourthPred]
    omega
  have hp := pow_mod_fiftyfour n
  rcases hres with h|h|h|h
  · have hm:n%54=10:=by omega
    have hn81:n%81=10:=by omega
    have hp81:2^n%81=2^10%81:=by rw [hp,hm]
    omega
  · have hm:n%54=53:=by omega
    have hn81:n%81=53:=by omega
    have hp81:2^n%81=2^53%81:=by rw [hp,hm]
    omega
  · have hm:n%54=10:=by omega
    have hn81:n%81=37:=by omega
    have hp81:2^n%81=2^10%81:=by rw [hp,hm]
    omega
  · have hm:n%54=53:=by omega
    have hn81:n%81=80:=by omega
    have hp81:2^n%81=2^53%81:=by rw [hp,hm]
    omega

#print axioms fourth_not_div81
end CascadeAgent10Mod81
