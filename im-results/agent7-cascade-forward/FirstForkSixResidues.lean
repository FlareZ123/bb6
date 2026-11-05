import FirstForkSix
set_option maxHeartbeats 0
set_option maxRecDepth 16384
set_option exponentiation.threshold 10000

namespace CascadeFirstFork
open CascadeResetInverse CascadeUniformFatal CascadeManyShield

/-- The period 4374 simultaneously respects 2^n mod 2187 and n mod 2187. -/
private theorem pow_period_4374 (n:Nat):
    2^(n+4374)%2187=2^n%2187:=by
  rw [Nat.pow_add]
  have hp:2^4374%2187=1:=by decide
  rw [Nat.mul_mod,hp]
  omega

private theorem pow_mod_4374 (n:Nat):
    2^n%2187=2^(n%4374)%2187:=by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn:n<4374
    · simp [Nat.mod_eq_of_lt hn]
    · have hm:n-4374<n:=by omega
      have he:n=(n-4374)+4374:=by omega
      rw [he,pow_period_4374]
      rw [ih (n-4374) hm]
      have hemod:((n-4374)+4374)%4374=(n-4374)%4374:=by omega
      rw [hemod]

/-- A genuine fatal-height output has a 3^7 factor on two infinite
    congruence classes, including the concrete example n=491. -/
theorem fatal_div2187_special (n:Nat) (hn:10≤n)
    (hres:n%4374=491 ∨ n%4374=3208):
    (2*fatal n+5)%2187=0 :=by
  have hf:=fatal_close n (by omega)
  have hp:=pow_mod_4374 n
  rcases hres with h|h
  · have hmod:2^n%2187=1490:=by
      rw [hp,h]
    omega
  · have hmod:2^n%2187=529:=by
      rw [hp,h]
    omega

/-- Similarly, n=83 lies in a quantified infinite family for the
    second forced even fatal ancestor. -/
theorem second_div2187_special (n:Nat) (hn:10≤n)
    (hres:n%4374=83 ∨ n%4374=1906):
    (2*secondPred n+5)%2187=0 :=by
  have hf:=second_close n hn
  have hp:=pow_mod_4374 n
  rcases hres with h|h
  · have hmod:2^n%2187=968:=by
      rw [hp,h]
    omega
  · have hmod:2^n%2187=331:=by
      rw [hp,h]
    omega

theorem fatal_six_parent (n:Nat) (hn:10≤n)
    (hres:n%4374=491 ∨ n%4374=3208) :
    ResetParent (oddPre6 n (fatal n)) (fatal n) :=
  near_top_has_tsix n (fatal n) (n+4) hn
    (fatal_close n (by omega)) (tight_fatal n hn)
    (fatal_div2187_special n hn hres)

theorem second_six_parent (n:Nat) (hn:10≤n)
    (hres:n%4374=83 ∨ n%4374=1906) :
    ResetParent (oddPre6 n (secondPred n)) (secondPred n) :=
  near_top_has_tsix n (secondPred n) (7*n+13) hn
    (second_close n hn) (tight_second n hn)
    (second_div2187_special n hn hres)

#print axioms fatal_div2187_special
#print axioms second_div2187_special
#print axioms fatal_six_parent
#print axioms second_six_parent
end CascadeFirstFork
