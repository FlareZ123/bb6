import F321BackwardBarrier
import Lean.Elab.Tactic.Omega

/-!
A forward all-time invariant of the exact F321 source-counter return map.
Apart from the initial seed (1,1), second counter d is 1 mod 3 exactly
when total a+d is odd, and 2 mod 3 exactly when a+d is even.
The actual halting gate has a=d+1 and hence odd total, so its d must be
1 mod 3. This strengthens nonzero-mod3 by excluding d≡2 as well.
-/

namespace BB6.Agent2F321Phase
open BB6.Agent31F321Density

def Phase (a d:Nat) : Prop :=
  ((a+d)%2=1 ∧ d%3=1) ∨ ((a+d)%2=0 ∧ d%3=2)

def Safe (a d:Nat) : Prop :=
  Phase a d ∨ (a=1 ∧ d=1)

theorem phase_preserved
    {a d A D:Nat} (h:CounterMove a d A D)
    (hp:Phase a d) : Phase A D := by
  dsimp [Phase] at hp ⊢
  cases h with
  | high a d hg =>
    rcases hp with h1 | h2
    · right; constructor <;> omega
    · left; constructor <;> omega
  | equal a =>
    left; constructor <;> omega
  | far a d h1 h2 =>
    rcases hp with h1p | h2p
    · left; constructor <;> omega
    · right; constructor <;> omega
  | middleEven a d h1 h2 hm =>
    right; constructor <;> omega
  | middleOdd a d h1 h2 hm =>
    left; constructor <;> omega

theorem safe_preserved
    {a d A D:Nat} (h:CounterMove a d A D)
    (hs:Safe a d) : Safe A D := by
  rcases hs with hp | hseed
  · exact Or.inl (phase_preserved h hp)
  · rcases hseed with ⟨ha,hd⟩
    subst a; subst d
    cases h with
    | high a d hg => omega
    | equal a => exact Or.inl (by decide)
    | far a d h1 h2 => omega
    | middleEven a d h1 h2 hm => omega
    | middleOdd a d h1 h2 hm => omega

theorem safe_from_seed
    {n a d:Nat} (hr:CounterReach 1 1 n a d) : Safe a d := by
  induction hr with
  | nil => exact Or.inr ⟨rfl,rfl⟩
  | step hr hm ih => exact safe_preserved hm ih

/-- A source-counter halt at H_d=(d+1,d), from the exact (1,1) seed,
can ONLY have d ≡ 1 (mod 3). This applies at all finite run lengths. -/
theorem terminal_requires_one_mod3 (d:Nat) :
    ∀ n, CounterReach 1 1 n (d+1) d → d%3=1 := by
  intro n hr
  rcases safe_from_seed hr with hp | hseed
  · rcases hp with h1 | h2
    · exact h1.2
    · have hodd : (d+1+d)%2=1 := by omega
      omega
  · omega

theorem no_other_mod3_terminal (d:Nat) (hd:d%3≠1) :
    ∀ n, ¬CounterReach 1 1 n (d+1) d := by
  intro n hr
  exact hd (terminal_requires_one_mod3 d n hr)

#print axioms phase_preserved
#print axioms safe_preserved
#print axioms safe_from_seed
#print axioms terminal_requires_one_mod3
#print axioms no_other_mod3_terminal

end BB6.Agent2F321Phase
