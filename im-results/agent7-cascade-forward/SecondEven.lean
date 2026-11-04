import UniqueEvenBand

namespace CascadeUniformFatal
open CascadeResetInverse CascadeManyShield CascadeSweep

def secondPred (n : Nat) : Nat := 4*2^n-7*n-13

private theorem three_n_six_le_pow (n : Nat) (hn : 5 ≤ n) :
    3*n+6 ≤ 2^n := by
  have h : ∀ k : Nat, 3*(k+5)+6 ≤ 2^(k+5) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
        rw [show k+1+5=k+5+1 by omega,Nat.pow_succ]
        omega
  have he : n=(n-5)+5 := by omega
  rw [he]
  exact h (n-5)

private theorem two_pow_mod_three (n : Nat) :
    2^n%3=1 ∨ 2^n%3=2 := by
  induction n with
  | zero => exact Or.inl (by decide)
  | succ n ih =>
      rw [Nat.pow_succ, Nat.mul_mod]
      rcases ih with h|h
      · exact Or.inr (by simp [h])
      · exact Or.inl (by simp [h])

theorem first_even_parent_not_odd_mod3 (n : Nat) (hn : 4 ≤ n) :
    evenPred n%3 ≠ 2 := by
  have hl := n_plus_three_le_pow n hn
  have heq : evenPred n+3*n+7=4*2^n := by
    dsimp [evenPred]
    omega
  rcases two_pow_mod_three n with h|h
  · omega
  · omega

theorem second_even_parent_exists (n : Nat) (hn : 5 ≤ n) :
    ResetParent (secondPred n) (evenPred n) := by
  have hp : 3*n+6 ≤ 2^n := three_n_six_le_pow n hn
  have he : 2^n = 2*2^(n-1) := by
    have he0 : 2^n = 2^((n-1)+1) := congrArg (fun m : Nat => 2^m) (by omega)
    rw [Nat.pow_succ] at he0
    omega
  have hbig : 7*n+13 ≤ 4*2^n := by omega
  have hlow : 6*2^(n-1)-1 ≤ evenPred n := by
    dsimp [evenPred]
    rw [he]
    omega
  have hhigh : evenPred n ≤ 8*2^(n-1)-3 := by
    dsimp [evenPred]
    rw [he]
    omega
  have hrelation : 2*evenPred n = 8*2^(n-1)+secondPred n+(n-1) := by
    dsimp [evenPred,secondPred]
    rw [he]
    omega
  exact Or.inl ⟨n-1,⟨hlow,hhigh⟩,hrelation⟩

theorem second_even_parent_unique (q n : Nat) (hn : 5 ≤ n)
    (hq : ResetParent q (evenPred n)) :
    q = secondPred n := by
  have hp : 3*n+6 ≤ 2^n := three_n_six_le_pow n hn
  have he : 2^n = 2*2^(n-1) := by
    have he0 : 2^n = 2^((n-1)+1) := congrArg (fun m : Nat => 2^m) (by omega)
    rw [Nat.pow_succ] at he0
    omega
  have hl : 6*2^(n-1)-1 ≤ evenPred n := by
    dsimp [evenPred]
    rw [he]
    omega
  have hu : evenPred n ≤ 8*2^(n-1)-3 := by
    dsimp [evenPred]
    rw [he]
    omega
  have hbig : 7*n+13 ≤ 4*2^n := by omega
  have hrel : 2*evenPred n = 8*2^(n-1)+secondPred n+(n-1) := by
    dsimp [evenPred,secondPred]
    rw [he]
    omega
  exact any_parent_equals_even (evenPred n) (n-1) (secondPred n) q
    ⟨hl,hu⟩ hrel (first_even_parent_not_odd_mod3 n (by omega)) hq

/-- For every n>=5, the forced even first predecessor of the fatal
    height has a unique further even first-reset predecessor. The source
    reachability problem for these two heights is exactly equivalent. -/
theorem first_even_reachable_iff_second_even
    (n : Nat) (hn : 5 ≤ n) :
    ReachC (2,0) (evenPred n,0) ↔ ReachC (2,0) (secondPred n,0) := by
  have hparent : ResetParent (secondPred n) (evenPred n) :=
    second_even_parent_exists n hn
  have hne : evenPred n ≠ 2 := by
    have hp : 3*n+6≤2^n := three_n_six_le_pow n hn
    dsimp [evenPred]
    omega
  constructor
  · intro hr
    have hc : ResetChain 2 (evenPred n) := (root_reset_chain_iff (evenPred n)).mp hr
    obtain ⟨q,hchain,hp⟩ := reset_chain_last hc hne
    have he : q=secondPred n := second_even_parent_unique q n hn hp
    rw [he] at hchain
    exact (root_reset_chain_iff (secondPred n)).mpr hchain
  · intro hr
    have hc : ResetChain 2 (secondPred n) :=
      (root_reset_chain_iff (secondPred n)).mp hr
    exact (root_reset_chain_iff (evenPred n)).mpr (ResetChain.append hc hparent)

/-- Two forced first-reset inverse levels, uniformly in four full
    modulo-18 classes, with genuine original source-C blank-root semantics. -/
theorem genuine_fatal_iff_second_even
    (n : Nat) (hn : 10 ≤ n)
    (hres : n%18=10 ∨ n%18=11 ∨ n%18=16 ∨ n%18=17) :
    ReachC (2,0) (fatal n,0) ↔
      ReachC (2,0) (secondPred n,0) :=
  (genuine_fatal_iff_unique_even_parent n (by omega) hres).trans
    (first_even_reachable_iff_second_even n (by omega))

#print axioms first_even_parent_not_odd_mod3
#print axioms second_even_parent_unique
#print axioms genuine_fatal_iff_second_even
end CascadeUniformFatal
