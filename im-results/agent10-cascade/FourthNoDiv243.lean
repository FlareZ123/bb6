import FourthThirdBranch
set_option maxHeartbeats 0
namespace CascadeAgent10Mod243
open CascadeAgent10Four CascadeAgent10FourthBranch

private theorem pow_period_162 (n:Nat) : 2^(n+162)%243=2^n%243:=by
  rw [Nat.pow_add]
  simp [Nat.mul_mod]

private theorem pow_mod_162 (n:Nat) : 2^n%243=2^(n%162)%243:=by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn:n<162
    · simp [Nat.mod_eq_of_lt hn]
    · have hm:n-162<n:=by omega
      have he:n=(n-162)+162:=by omega
      rw [he,pow_period_162]
      rw [ih (n-162) hm]
      have hemod:((n-162)+162)%162=(n-162)%162:=by omega
      rw [hemod]

/-- Four of six mod486 subcases of the two exceptional mod162 sectors
    have *exactly* four factors of three in the odd-gate numerator. -/
theorem fourth_not_div243 (n:Nat) (hn:64≤n)
    (hres:n%486=64 ∨ n%486=226 ∨ n%486=269 ∨ n%486=431) :
    (2*fourthPred n+5)%243≠0 := by
  have hb := fifth_growth n (by omega)
  have heq : 2*fourthPred n+5+62*n+93=8*2^n := by
    dsimp [fourthPred]
    omega
  have hp := pow_mod_162 n
  rcases hres with h|h|h|h
  · have hm:n%162=64:=by omega
    have hn243:n%243=64:=by omega
    have hp243:2^n%243=2^64%243:=by rw [hp,hm]
    omega
  · have hm:n%162=64:=by omega
    have hn243:n%243=226:=by omega
    have hp243:2^n%243=2^64%243:=by rw [hp,hm]
    omega
  · have hm:n%162=107:=by omega
    have hn243:n%243=26:=by omega
    have hp243:2^n%243=2^107%243:=by rw [hp,hm]
    omega
  · have hm:n%162=107:=by omega
    have hn243:n%243=188:=by omega
    have hp243:2^n%243=2^107%243:=by rw [hp,hm]
    omega

#print axioms fourth_not_div243
end CascadeAgent10Mod243
