import FirstInverseComplete
import ResetChain
import PeriodicWord

namespace CascadePeriodic
open CascadeResetInverse

theorem source_reset_parent_iff_unified (h u : Nat) :
    ResetParent h u ↔ ∃ k a, Unified h u k a := by
  exact grammar_iff_unified h u

theorem unified_is_source_reset_parent {h u k a : Nat}
    (hu : Unified h u k a) : ResetParent h u :=
  (grammar_iff_unified h u).mpr ⟨k,a,hu⟩

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
    ∀ n, CascadeSource.ReachC (2,0) (h n,0) := by
  intro n
  exact reset_chain_to_cpath (source_periodic_root_chain w h k h0 hf n)

#print axioms source_reset_parent_iff_unified
#print axioms sourceFollows_to_follows
#print axioms sourceFollows_resetChain
#print axioms source_periodic_word_divisibility
#print axioms source_periodic_root_reach
end CascadePeriodic
