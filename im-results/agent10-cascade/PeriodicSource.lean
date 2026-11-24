import FirstInverseComplete
import ResetChain
import ResetParentStrict
import PeriodicWord

namespace CascadePeriodic
open CascadeResetInverse CascadeSource CascadeSweep

/-- The standalone grammar is definitionally the unchanged source ResetParent. -/
theorem source_reset_parent_iff_unified (h u : Nat) :
    ResetParent h u ↔ ∃ k a, Unified h u k a := by
  exact grammar_iff_unified h u

theorem unified_is_source_reset_parent {h u k a : Nat}
    (hu : Unified h u k a) : ResetParent h u :=
  (grammar_iff_unified h u).mpr ⟨k,a,hu⟩

/-- A finite token word whose every step satisfies the exact source Unified
    relation. Its edges are therefore genuine ResetParent edges. -/
inductive SourceFollows : List Token → Nat → Nat → Nat → Nat → Prop where
  | nil (h k : Nat) : SourceFollows [] h k h k
  | cons {a δ k l : Nat} {w : List Token} {h x u : Nat}
      (he : Unified h x k a)
      (ht : SourceFollows w x (k+δ) u l) :
      SourceFollows ((a,δ)::w) h k u l

theorem sourceFollows_to_follows {w : List Token} {h u k l : Nat}
    (hs : SourceFollows w h k u l) :
    Follows w ((2*h+5 : Nat) : Int) k ((2*u+5 : Nat) : Int) l := by
  induction hs with
  | nil h k => exact Follows.nil _ _
  | @cons a δ k l w h x u he ht ih =>
    have he' : (2:Int)^(a+1)*((2*x+5 : Nat) : Int) =
        (3:Int)^a*((2*h+5 : Nat) + 16*2^k + 2*k + 5) := by
      exact_mod_cast he.2
    exact Follows.cons he' ih

private theorem resetChain_trans {s m t : Nat}
    (h1 : ResetChain s m) (h2 : ResetChain m t) : ResetChain s t := by
  induction h2 generalizing s with
  | root => exact h1
  | append hr hp ih => exact ResetChain.append (ih h1) hp

theorem sourceFollows_resetChain {w : List Token} {h u k l : Nat}
    (hs : SourceFollows w h k u l) : ResetChain h u := by
  induction hs with
  | nil h k => exact ResetChain.root
  | @cons a δ k l w h x u he ht ih =>
    have hp : ResetParent h x := unified_is_source_reset_parent he
    have hfirst : ResetChain h x := ResetChain.append ResetChain.root hp
    exact resetChain_trans hfirst ih

theorem sourceFollows_head_valid {a δ : Nat} {w : List Token} {h u k l : Nat}
    (hs : SourceFollows ((a,δ)::w) h k u l) : Valid h k := by
  cases hs with
  | cons he ht => exact he.1

private theorem resetChain_le {s u : Nat} (hc : ResetChain s u) : s ≤ u := by
  induction hc with
  | root => omega
  | append hr hp ih =>
    have hlt := reset_parent_strict _ _ hp
    exact Nat.le_trans ih (Nat.le_of_lt hlt)

theorem sourceFollows_nonempty_strict {a δ : Nat} {w : List Token} {h u k l : Nat}
    (hs : SourceFollows ((a,δ)::w) h k u l) : h < u := by
  cases hs with
  | @cons a δ k l w h x u he ht =>
    have hp : ResetParent h x := unified_is_source_reset_parent he
    have hlt : h < x := reset_parent_strict h x hp
    have htail : ResetChain x u := sourceFollows_resetChain ht
    have hle : x ≤ u := resetChain_le htail
    exact Nat.lt_of_lt_of_le hlt hle

/-- Any infinite source path repeating a nonempty token word has strictly
    positive level drift per word: zero drift would trap a strictly increasing
    sequence in one finite Valid band. -/
theorem source_periodic_increment_pos (a δ : Nat) (w : List Token)
    (h k : Nat → Nat)
    (hf : ∀ j, SourceFollows ((a,δ)::w) (h j) (k j) (h (j+1)) (k (j+1))) :
    0 < (coeff ((a,δ)::w)).d := by
  let D := (coeff ((a,δ)::w)).d
  have hlevel (j : Nat) : k (j+1) = k j + D := by
    have hF := sourceFollows_to_follows (hf j)
    exact (follows_affine hF).1
  have hvalid (j : Nat) : Valid (h j) (k j) := sourceFollows_head_valid (hf j)
  have hstrict (j : Nat) : h j < h (j+1) := sourceFollows_nonempty_strict (hf j)
  by_cases hD0 : D = 0
  · have hconst : ∀ j, k j = k 0 := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih => rw [hlevel j, hD0, ih]; omega
    have hbound (j : Nat) : h j < 8*2^(k 0) := by
      have hv := hvalid j
      rw [hconst j] at hv
      rcases hv with ⟨hl,hu⟩
      omega
    have hinc (j : Nat) : h 0 + j ≤ h j := by
      induction j with
      | zero => omega
      | succ j ih => have hs := hstrict j; omega
    have hb := hbound (8*2^(k 0))
    have hi := hinc (8*2^(k 0))
    omega
  · omega

theorem source_periodic_word_divisibility (a δ : Nat) (w : List Token)
    (h k : Nat → Nat)
    (hf : ∀ j, SourceFollows ((a,δ)::w) (h j) (k j) (h (j+1)) (k (j+1))) :
    let q := coeff ((a,δ)::w)
    ∀ j, q.p*2^q.d-q.r ∣ (16*q.s)*2^(k j)*(2^q.d-1)^2 := by
  let x : Nat → Int := fun j => ((2*h j+5 : Nat) : Int)
  have hF (j : Nat) : Follows ((a,δ)::w) (x j) (k j) (x (j+1)) (k (j+1)) := by
    simpa [x] using sourceFollows_to_follows (hf j)
  simpa [x] using repeated_word_divisibility a δ w x k hF

theorem source_periodic_root_chain (w : List Token) (h k : Nat → Nat)
    (h0 : h 0 = 2)
    (hf : ∀ j, SourceFollows w (h j) (k j) (h (j+1)) (k (j+1))) :
    ∀ n, ResetChain 2 (h n) := by
  intro n
  induction n with
  | zero => rw [h0]; exact ResetChain.root
  | succ n ih =>
    have hc : ResetChain (h n) (h (n+1)) := sourceFollows_resetChain (hf n)
    exact resetChain_trans ih hc

theorem source_periodic_root_reach (w : List Token) (h k : Nat → Nat)
    (h0 : h 0 = 2)
    (hf : ∀ j, SourceFollows w (h j) (k j) (h (j+1)) (k (j+1))) :
    ∀ n, ReachC (2,0) (h n,0) := by
  intro n
  exact reset_chain_to_cpath (source_periodic_root_chain w h k h0 hf n)

#print axioms source_reset_parent_iff_unified
#print axioms sourceFollows_to_follows
#print axioms sourceFollows_resetChain
#print axioms source_periodic_increment_pos
#print axioms source_periodic_word_divisibility
#print axioms source_periodic_root_reach
end CascadePeriodic
