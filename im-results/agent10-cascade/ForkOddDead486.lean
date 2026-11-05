import ForkOddDead27
set_option maxHeartbeats 0
set_option maxRecDepth 8192
namespace CascadeForkOddDead486
open CascadeSweep CascadeManyShield CascadeAgent10FourthBranch CascadeAgent10ExactlyTwo
open CascadeForkOddDead CascadeForkOddDead27

private theorem pow_period_162 (n : Nat) : 2^(n+162)%243 = 2^n%243 := by
  rw [Nat.pow_add]
  simp [Nat.mul_mod]

private theorem pow_mod_162 (n : Nat) : 2^n%243 = 2^(n%162)%243 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n < 162
    · simp [Nat.mod_eq_of_lt hn]
    · have hm : n-162<n := by omega
      have he : n=(n-162)+162 := by omega
      rw [he,pow_period_162]
      rw [ih (n-162) hm]
      have hemod : ((n-162)+162)%162=(n-162)%162 := by omega
      rw [hemod]

private theorem residue_table :
    ∀ r:Fin 486, (r.val%54=17 ∨ r.val%54=28) →
    r.val ≠395 → r.val≠460 →
    (514*r.val+753)%243 ≠ (28*2^(r.val%162))%243 := by decide

private theorem modulo_equation (n v P:Nat)
    (heq:9*v+257*n+399=14*P)
    (hbad:(2*v+5)%27=0) :
    (514*n+753)%243=(28*P)%243 := by
  have hmult : 9*(2*v+5)+514*n+753=28*P := by omega
  have hzero : (9*(2*v+5))%243=0 := by omega
  omega

theorem odd_secondary_nondiv27 (n:Nat) (hn:13≤n)
    (hres:n%54=17 ∨ n%54=28)
    (h395:n%486≠395) (h460:n%486≠460) :
    (2*oddPre n+5)%27 ≠ 0 := by
  have h4 : n%54=17 ∨ n%54=28 ∨ n%54=35 ∨ n%54=46 := by omega
  have heq := odd_linear n hn h4
  have hP := pow_mod_162 n
  have hm162 : n%162=(n%486)%162 := by omega
  have hm243 : (514*n+753)%243=(514*(n%486)+753)%243 := by omega
  have hperiod : (28*2^n)%243=(28*2^((n%486)%162))%243 := by
    rw [Nat.mul_mod, hP, hm162]
    simp [Nat.mul_mod]
  have hsmall : (n%486)%54=n%54 := by omega
  intro hbad
  have hequal : (514*n+753)%243=(28*2^n)%243 :=
    modulo_equation n (oddPre n) (2^n) heq hbad
  have hvalid : (514*(n%486)+753)%243 ≠
      (28*2^((n%486)%162))%243 := by
    have hr : n%486<486 := Nat.mod_lt _ (by decide)
    have hfin := residue_table ⟨n%486,hr⟩
    simp only at hfin
    exact hfin (by rw [hsmall];exact hres) h395 h460
  exact hvalid (hm243.symm.trans (hequal.trans hperiod))

theorem rooted_odd_fork_dead_34_of_36 (n:Nat) (hn:13≤n)
    (hres:n%54=17 ∨ n%54=28 ∨ n%54=35 ∨ n%54=46)
    (h395:n%486≠395) (h460:n%486≠460) :
    ¬ReachC (2,0) (oddPre n,0) := by
  rcases hres with h17|h28|h35|h46
  · exact odd_fork_unreachable_no27 n hn (Or.inl h17)
      (odd_secondary_nondiv27 n hn (Or.inl h17) h395 h460)
  · exact odd_fork_unreachable_no27 n hn (Or.inr (Or.inl h28))
      (odd_secondary_nondiv27 n hn (Or.inr h28) h395 h460)
  · exact odd_fork_branch_unreachable n hn (Or.inl h35)
  · exact odd_fork_branch_unreachable n hn (Or.inr h46)

theorem fatal_iff_even_34_of_36 (n:Nat) (hn:13≤n)
    (hres:n%54=17 ∨ n%54=28 ∨ n%54=35 ∨ n%54=46)
    (h395:n%486≠395) (h460:n%486≠460) :
    ReachC (2,0) (fatal n,0) ↔ ReachC (2,0) (evenPre n,0) := by
  have hprior:=genuine_fatal_iff_two_parent_roots n (by omega) hres
  constructor
  · intro hr
    rcases hprior.mp hr with ho|he
    · exact False.elim ((rooted_odd_fork_dead_34_of_36 n hn hres h395 h460) ho)
    · exact he
  · intro he
    exact hprior.mpr (Or.inr he)

#print axioms rooted_odd_fork_dead_34_of_36
#print axioms fatal_iff_even_34_of_36
end CascadeForkOddDead486
