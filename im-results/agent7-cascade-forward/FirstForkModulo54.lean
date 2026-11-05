import FirstForkExactTwo

namespace CascadeFirstFork
open CascadeResetInverse CascadeUniformFatal CascadeManyShield

private theorem pow_period_eighteen (n : Nat) :
    2^(n+18)%27=2^n%27 := by
  rw [Nat.pow_add]
  simp [Nat.mul_mod]

private theorem pow_mod_eighteen (n : Nat) :
    2^n%27=2^(n%18)%27 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn:n<18
    · simp [Nat.mod_eq_of_lt hn]
    · have hm:n-18<n:=by omega
      have he:n=(n-18)+18:=by omega
      rw [he,pow_period_eighteen]
      rw [ih (n-18) hm]
      have hmod:((n-18)+18)%18=(n-18)%18:=by omega
      rw [hmod]

/-- Four mod54 fatal subclasses have precisely v3(2fatal(n)+5)=2. -/
theorem fatal_not_div27 (n:Nat) (hn:4≤n)
    (hres:n%54=4 ∨ n%54=23 ∨ n%54=40 ∨ n%54=41) :
    (2*fatal n+5)%27≠0 := by
  have hf:=fatal_close n hn
  have hp:=pow_mod_eighteen n
  rcases hres with h|h|h|h
  · have hm:n%18=4:=by omega
    have hm27:2^n%27=2^4%27:=by rw [hp,hm]
    omega
  · have hm:n%18=5:=by omega
    have hm27:2^n%27=2^5%27:=by rw [hp,hm]
    omega
  · have hm:n%18=4:=by omega
    have hm27:2^n%27=2^4%27:=by rw [hp,hm]
    omega
  · have hm:n%18=5:=by omega
    have hm27:2^n%27=2^5%27:=by rw [hp,hm]
    omega

/-- Four mod54 second-predecessor subclasses have exactly two factors 3. -/
theorem second_not_div27 (n:Nat) (hn:10≤n)
    (hres:n%54=11 ∨ n%54=34 ∨ n%54=47 ∨ n%54=52) :
    (2*secondPred n+5)%27≠0 := by
  have hf:=second_close n hn
  have hp:=pow_mod_eighteen n
  rcases hres with h|h|h|h
  · have hm:n%18=11:=by omega
    have hm27:2^n%27=2^11%27:=by rw [hp,hm]
    omega
  · have hm:n%18=16:=by omega
    have hm27:2^n%27=2^16%27:=by rw [hp,hm]
    omega
  · have hm:n%18=11:=by omega
    have hm27:2^n%27=2^11%27:=by rw [hp,hm]
    omega
  · have hm:n%18=16:=by omega
    have hm27:2^n%27=2^16%27:=by rw [hp,hm]
    omega

theorem fatal_parents_exactly_two (q n:Nat) (hn:4≤n)
    (hres:n%54=4 ∨ n%54=23 ∨ n%54=40 ∨ n%54=41) :
    ResetParent q (fatal n) ↔
      q=oddPre n (fatal n) ∨ q=evenPre n (n+4) := by
  have h18:n%18=4 ∨ n%18=5:=by omega
  exact near_top_exact_two n (fatal n) (n+4) q hn (by omega)
    (fatal_close n hn) (fatal_size n hn) (fatal_divnine n hn h18)
    (fatal_not_div27 n hn hres)

theorem second_parents_exactly_two (q n:Nat) (hn:10≤n)
    (hres:n%54=11 ∨ n%54=34 ∨ n%54=47 ∨ n%54=52) :
    ResetParent q (secondPred n) ↔
      q=oddPre n (secondPred n) ∨ q=evenPre n (7*n+13) := by
  have h18:n%18=11 ∨ n%18=16:=by omega
  exact near_top_exact_two n (secondPred n) (7*n+13) q (by omega)
    (by omega) (second_close n hn) (second_size n hn)
    (second_divnine n hn h18) (second_not_div27 n hn hres)

/-- Every reached nonroot reset has a last source-certified edge. -/
theorem rooted_two_parents (u a b:Nat) (hu:u≠2)
    (ha:ResetParent a u) (hb:ResetParent b u)
    (hall:∀ q, ResetParent q u ↔ q=a∨q=b) :
    CascadeSweep.ReachC (2,0) (u,0) ↔
      CascadeSweep.ReachC (2,0) (a,0) ∨ CascadeSweep.ReachC (2,0) (b,0) := by
  constructor
  · intro hroot
    have hc:ResetChain 2 u := (root_reset_chain_iff u).mp hroot
    obtain ⟨q,hchain,hparent⟩:=reset_chain_last hc hu
    rcases (hall q).mp hparent with h|h
    · left
      rw [h] at hchain
      exact (root_reset_chain_iff a).mpr hchain
    · right
      rw [h] at hchain
      exact (root_reset_chain_iff b).mpr hchain
  · intro h
    rcases h with h|h
    · have hc:ResetChain 2 a := (root_reset_chain_iff a).mp h
      exact (root_reset_chain_iff u).mpr (hc.append ha)
    · have hc:ResetChain 2 b := (root_reset_chain_iff b).mp h
      exact (root_reset_chain_iff u).mpr (hc.append hb)

theorem rooted_fatal_two_parents (n:Nat) (hn:4≤n)
    (hres:n%54=4 ∨ n%54=23 ∨ n%54=40 ∨ n%54=41) :
    CascadeSweep.ReachC (2,0) (fatal n,0) ↔
      CascadeSweep.ReachC (2,0) (oddPre n (fatal n),0) ∨
      CascadeSweep.ReachC (2,0) (evenPre n (n+4),0) := by
  have h18:n%18=4 ∨ n%18=5:=by omega
  have hno:fatal n≠2:=by
    have hpow:=n_plus_three_le_pow n hn
    dsimp [fatal]
    omega
  exact rooted_two_parents (fatal n) (oddPre n (fatal n))
    (evenPre n (n+4)) hno
    (fatal_has_odd_parent n hn h18)
    (even_parent_near_top n (fatal n) (n+4) hn (by omega)
      (fatal_close n hn) (fatal_size n hn))
    (fun q => fatal_parents_exactly_two q n hn hres)

theorem rooted_second_two_parents (n:Nat) (hn:10≤n)
    (hres:n%54=11 ∨ n%54=34 ∨ n%54=47 ∨ n%54=52) :
    CascadeSweep.ReachC (2,0) (secondPred n,0) ↔
      CascadeSweep.ReachC (2,0) (oddPre n (secondPred n),0) ∨
      CascadeSweep.ReachC (2,0) (evenPre n (7*n+13),0) := by
  have h18:n%18=11 ∨ n%18=16:=by omega
  have hno:secondPred n≠2:=by
    have hp:=second_size n hn
    dsimp [secondPred]
    omega
  exact rooted_two_parents (secondPred n) (oddPre n (secondPred n))
    (evenPre n (7*n+13)) hno
    (second_has_odd_parent n hn h18)
    (even_parent_near_top n (secondPred n) (7*n+13) (by omega)
      (by omega) (second_close n hn) (second_size n hn))
    (fun q => second_parents_exactly_two q n hn hres)

/-- Two forced exact reset edges precede the two-way fork for these classes. -/
theorem rooted_fatal_after_second (n:Nat) (hn:10≤n)
    (hres:n%54=11 ∨ n%54=34 ∨ n%54=47 ∨ n%54=52) :
    CascadeSweep.ReachC (2,0) (fatal n,0) ↔
      CascadeSweep.ReachC (2,0) (oddPre n (secondPred n),0) ∨
      CascadeSweep.ReachC (2,0) (evenPre n (7*n+13),0) := by
  have h18:n%18=11 ∨ n%18=16:=by omega
  have h18all:n%18=10 ∨ n%18=11 ∨ n%18=16 ∨ n%18=17:=by
    rcases h18 with h|h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  exact (genuine_fatal_iff_second_even n hn h18all).trans
    (rooted_second_two_parents n hn hres)

#print axioms fatal_parents_exactly_two
#print axioms second_parents_exactly_two
#print axioms rooted_fatal_two_parents
#print axioms rooted_second_two_parents
#print axioms rooted_fatal_after_second

end CascadeFirstFork
