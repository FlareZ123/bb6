import SourceCounter
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2F321Phase6
open BB6.Agent31F321Density

/-- Three parity/mod-6 classes containing every non-seed state of the
    authentic F321 source-counter orbit. -/
def Phase6 (a d : Nat) : Prop :=
  (a % 2 = 0 ∧ d % 6 = 1) ∨
  (a % 2 = 0 ∧ d % 6 = 2) ∨
  (a % 2 = 1 ∧ d % 6 = 5)

theorem phase6_preserved {a d A D : Nat}
    (hp : Phase6 a d) (hm : CounterMove a d A D) : Phase6 A D := by
  unfold Phase6 at hp ⊢
  rcases hp with h01 | h02 | h15
  · cases hm with
    | high d hg =>
        right; right
        omega
    | equal => omega
    | far d h1 h2 =>
        left
        omega
    | middleEven d h1 h2 hpar => omega
    | middleOdd d h1 h2 hpar =>
        left
        omega
  · cases hm with
    | high d hg =>
        left
        omega
    | equal =>
        left
        omega
    | far d h1 h2 =>
        right; left
        omega
    | middleEven d h1 h2 hpar =>
        right; left
        omega
    | middleOdd d h1 h2 hpar => omega
  · cases hm with
    | high d hg =>
        left
        omega
    | equal =>
        left
        omega
    | far d h1 h2 =>
        right; left
        omega
    | middleEven d h1 h2 hpar =>
        right; left
        omega
    | middleOdd d h1 h2 hpar => omega

/-- The seed has exactly one legal source move, into the first Phase6 class. -/
theorem seed_step_phase6 {A D : Nat} (hm : CounterMove 1 1 A D) : Phase6 A D := by
  unfold Phase6
  cases hm with
  | high d hg => omega
  | equal =>
      left
      omega
  | far d h1 h2 => omega
  | middleEven d h1 h2 hp => omega
  | middleOdd d h1 h2 hp => omega

/-- Minimal forward reachability relation over the exact published source map. -/
inductive Reach : Nat → Nat → Nat → Prop where
  | nil : Reach 0 1 1
  | step {n a d A D : Nat} (hr : Reach n a d) (hm : CounterMove a d A D) :
      Reach (n+1) A D

/-- Root-specific all-depth invariant: every positive-time authentic state lies
    in one of only three parity/mod-6 classes. -/
theorem root_phase6 {n a d : Nat} (hr : Reach n a d) :
    (n = 0 ∧ a = 1 ∧ d = 1) ∨ Phase6 a d := by
  induction hr with
  | nil => exact Or.inl ⟨rfl, rfl, rfl⟩
  | @step n a d A D hr hm ih =>
      right
      rcases ih with hseed | hp
      · rcases hseed with ⟨hn,ha,hd⟩
        subst n; subst a; subst d
        exact seed_step_phase6 hm
      · exact phase6_preserved hp hm

/-- Consequence used by reset dynamics: every reachable odd-middle predecessor
    has even first counter and d == 1 mod 6. -/
theorem reachable_middleOdd_shape {n a d : Nat} (hr : Reach n a d)
    (h1 : a < d) (hp : (d-a)%2 = 1) :
    a % 2 = 0 ∧ d % 6 = 1 := by
  have hphase := root_phase6 hr
  rcases hphase with hseed | hphase
  · rcases hseed with ⟨hn,ha,hd⟩
    subst a; subst d
    omega
  · unfold Phase6 at hphase
    rcases hphase with h01 | h02 | h15
    · exact h01
    · omega
    · omega

/-- Therefore every reachable middle-odd reset lands at d=1 with first counter
    6 modulo 8, a stronger reset congruence than the generic branch formula. -/
theorem reachable_middleOdd_reset_mod8 {n a d : Nat} (hr : Reach n a d)
    (h1 : a < d) (h2 : d < 3*a+1) (hp : (d-a)%2 = 1) :
    (4*a+6) % 8 = 6 := by
  have hs := reachable_middleOdd_shape hr h1 hp
  omega

/-- Any positive-time terminal gate compatible with the root invariant has
    d == 1 mod 6 and therefore d == 1 mod 3, recovering and sharpening the
    previous phase filter at the actual halt shape a=d+1. -/
theorem terminal_phase6 {n d : Nat} (hn : 0 < n) (hr : Reach n (d+1) d) :
    d % 6 = 1 := by
  have hphase := root_phase6 hr
  rcases hphase with hseed | hphase
  · omega
  · unfold Phase6 at hphase
    rcases hphase with h01 | h02 | h15
    · exact h01.2
    · omega
    · omega

#print axioms phase6_preserved
#print axioms root_phase6
#print axioms reachable_middleOdd_reset_mod8
#print axioms terminal_phase6
end BB6.Agent2F321Phase6
