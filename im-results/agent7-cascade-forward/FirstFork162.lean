import FirstForkAt81

namespace CascadeFirstFork
open CascadeResetInverse CascadeUniformFatal CascadeManyShield

private theorem pow_period_fiftyfour (n:Nat) : 2^(n+54)%81=2^n%81 := by
  rw [Nat.pow_add]
  simp [Nat.mul_mod]

theorem pow_mod_fiftyfour (n:Nat) :
    2^n%81=2^(n%54)%81 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn:n<54
    · simp [Nat.mod_eq_of_lt hn]
    · have hm:n-54<n:=by omega
      have he:n=(n-54)+54:=by omega
      rw [he,pow_period_fiftyfour]
      rw [ih (n-54) hm]
      have hmod:((n-54)+54)%54=(n-54)%54:=by omega
      rw [hmod]

private theorem mod27_nonzero_implies_mod81_nonzero (u:Nat)
    (h:(2*u+5)%27≠0) : (2*u+5)%81≠0 := by
  omega

theorem fatal_extra_not_div81 (n:Nat) (hn:4≤n)
    (hres:n%162=22 ∨ n%162=59 ∨ n%162=76 ∨ n%162=113) :
    (2*fatal n+5)%81≠0 := by
  have hf:=fatal_close n hn
  have hp:=pow_mod_fiftyfour n
  rcases hres with h|h|h|h
  · have hm:n%54=22:=by omega
    have hm81:2^n%81=2^22%81:=by rw [hp,hm]
    omega
  · have hm:n%54=5:=by omega
    have hm81:2^n%81=2^5%81:=by rw [hp,hm]
    omega
  · have hm:n%54=22:=by omega
    have hm81:2^n%81=2^22%81:=by rw [hp,hm]
    omega
  · have hm:n%54=5:=by omega
    have hm81:2^n%81=2^5%81:=by rw [hp,hm]
    omega

theorem second_extra_not_div81 (n:Nat) (hn:10≤n)
    (hres:n%162=16 ∨ n%162=29 ∨ n%162=70 ∨ n%162=137) :
    (2*secondPred n+5)%81≠0 := by
  have hf:=second_close n hn
  have hp:=pow_mod_fiftyfour n
  rcases hres with h|h|h|h
  · have hm:n%54=16:=by omega
    have hm81:2^n%81=2^16%81:=by rw [hp,hm]
    omega
  · have hm:n%54=29:=by omega
    have hm81:2^n%81=2^29%81:=by rw [hp,hm]
    omega
  · have hm:n%54=16:=by omega
    have hm81:2^n%81=2^16%81:=by rw [hp,hm]
    omega
  · have hm:n%54=29:=by omega
    have hm81:2^n%81=2^29%81:=by rw [hp,hm]
    omega

/-- Four additional classes have exactly the two explicit parents. -/
theorem fatal_extra_parents_exactly_two (q n:Nat) (hn:4≤n)
    (hres:n%162=22 ∨ n%162=59 ∨ n%162=76 ∨ n%162=113) :
    ResetParent q (fatal n) ↔
      q=oddPre n (fatal n) ∨ q=evenPre n (n+4) := by
  have h18:n%18=4 ∨ n%18=5:=by omega
  exact near_top_exact_two_at81 n (fatal n) (n+4) q hn (by omega)
    (fatal_close n hn) (fatal_size n hn) (fatal_divnine n hn h18)
    (fatal_extra_not_div81 n hn hres)

theorem second_extra_parents_exactly_two (q n:Nat) (hn:10≤n)
    (hres:n%162=16 ∨ n%162=29 ∨ n%162=70 ∨ n%162=137) :
    ResetParent q (secondPred n) ↔
      q=oddPre n (secondPred n) ∨ q=evenPre n (7*n+13) := by
  have h18:n%18=11 ∨ n%18=16:=by omega
  exact near_top_exact_two_at81 n (secondPred n) (7*n+13) q (by omega)
    (by omega) (second_close n hn) (second_size n hn)
    (second_divnine n hn h18) (second_extra_not_div81 n hn hres)

theorem rooted_fatal_extra (n:Nat) (hn:4≤n)
    (hres:n%162=22 ∨ n%162=59 ∨ n%162=76 ∨ n%162=113) :
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
    (fun q => fatal_extra_parents_exactly_two q n hn hres)

theorem rooted_fatal_after_second_extra (n:Nat) (hn:10≤n)
    (hres:n%162=16 ∨ n%162=29 ∨ n%162=70 ∨ n%162=137) :
    CascadeSweep.ReachC (2,0) (fatal n,0) ↔
      CascadeSweep.ReachC (2,0) (oddPre n (secondPred n),0) ∨
      CascadeSweep.ReachC (2,0) (evenPre n (7*n+13),0) := by
  have h18:n%18=11 ∨ n%18=16:=by omega
  have h18all:n%18=10 ∨ n%18=11 ∨ n%18=16 ∨ n%18=17:=by
    rcases h18 with h|h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  have hno:secondPred n≠2:=by
    have hp:=second_size n hn
    dsimp [secondPred]
    omega
  have hroot: CascadeSweep.ReachC (2,0) (secondPred n,0) ↔
      CascadeSweep.ReachC (2,0) (oddPre n (secondPred n),0) ∨
      CascadeSweep.ReachC (2,0) (evenPre n (7*n+13),0) := by
    exact rooted_two_parents (secondPred n) (oddPre n (secondPred n))
      (evenPre n (7*n+13)) hno
      (second_has_odd_parent n hn h18)
      (even_parent_near_top n (secondPred n) (7*n+13) (by omega)
        (by omega) (second_close n hn) (second_size n hn))
      (fun q => second_extra_parents_exactly_two q n hn hres)
  exact (genuine_fatal_iff_second_even n hn h18all).trans hroot

#print axioms fatal_extra_parents_exactly_two
#print axioms second_extra_parents_exactly_two
#print axioms rooted_fatal_extra
#print axioms rooted_fatal_after_second_extra

#print axioms fatal_extra_not_div81
#print axioms second_extra_not_div81
end CascadeFirstFork
