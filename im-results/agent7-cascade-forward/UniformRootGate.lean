import UniformFatalMod9
import ResetChain

namespace CascadeUniformFatal
open CascadeResetInverse CascadeManyShield CascadeSweep

def evenPred (n : Nat) : Nat := 4*2^n-3*n-7

private theorem n_plus_three_le_pow (n : Nat) (hn : 4 ≤ n) :
    n+3 ≤ 2^n := by
  have h : ∀ k : Nat, k+7 ≤ 2^(k+4) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
        rw [show k+1+4=k+4+1 by omega, Nat.pow_succ]
        omega
  have he : n=(n-4)+4 := by omega
  rw [he]
  exact h (n-4)

theorem fatal_even_parent_exists (n : Nat) (hn : 4 ≤ n) :
    ResetParent (evenPred n) (fatal n) := by
  have hp : n+3 ≤ 2^n := n_plus_three_le_pow n hn
  have he : 2^n = 2*2^(n-1) := by
    rw [show n=(n-1)+1 by omega, Nat.pow_succ]
    omega
  have hbig : 3*n+7 ≤ 4*2^n := by omega
  have hlow : 6*2^(n-1)-1 ≤ fatal n := by
    dsimp [fatal]
    rw [he]
    omega
  have hhigh : fatal n ≤ 8*2^(n-1)-3 := by
    dsimp [fatal]
    rw [he]
    omega
  have hrelation : 2*fatal n = 8*2^(n-1)+evenPred n+(n-1) := by
    dsimp [fatal, evenPred]
    rw [he]
    omega
  exact Or.inl ⟨n-1,⟨hlow,hhigh⟩,hrelation⟩

/-- A genuine blank-root fatal reset in these four mod18 classes
    is reachable iff its forced unique lower even predecessor is reachable.
    No assumption of a finite search cutoff occurs. -/
theorem genuine_fatal_iff_unique_even_parent
    (n : Nat) (hn : 4 ≤ n)
    (hres : n%18=10 ∨ n%18=11 ∨ n%18=16 ∨ n%18=17) :
    ReachC (2,0) (fatal n,0) ↔
      ReachC (2,0) (evenPred n,0) := by
  have hparent : ResetParent (evenPred n) (fatal n) :=
    fatal_even_parent_exists n hn
  have hnsmall : fatal n ≠ 2 := by
    have hl := n_plus_three_le_pow n hn
    dsimp [fatal]
    omega
  constructor
  · intro hr
    have hc : ResetChain 2 (fatal n) := (root_reset_chain_iff (fatal n)).mp hr
    cases hc with
    | root =>
        exact False.elim (hnsmall rfl)
    | @append h u hchain hp =>
        have hforced : h=evenPred n := fatal_only_even_parent h n hn hres hp
        rw [hforced] at hchain
        exact (root_reset_chain_iff (evenPred n)).mpr hchain
  · intro hr
    have hc : ResetChain 2 (evenPred n) :=
      (root_reset_chain_iff (evenPred n)).mp hr
    exact (root_reset_chain_iff (fatal n)).mpr (ResetChain.append hc hparent)

#print axioms fatal_even_parent_exists
#print axioms genuine_fatal_iff_unique_even_parent
end CascadeUniformFatal
