import BB429Rank
import Lean.Elab.Tactic.Omega
namespace BB429Full27
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000
/-- Executable finite counterexample to a modulo-27 halt-free global invariant. -/
def witness : Nat → Nat × Nat × Nat × Nat
  | 0 => (999, 153, 445, 889)
  | 1 => (190, 29, 93, 185)
  | 2 => (29, 2, 9, 17)
  | 3 => (1272, 107, 445, 889)
  | 4 => (814, 190, 445, 889)
  | 5 => (167, 4, 45, 89)
  | 6 => (60, 58, 93, 185)
  | 7 => (34, 63, 93, 185)
  | 8 => (8, 1, 3, 5)
  | 9 => (171, 41, 93, 185)
  | 10 => (982, 158, 445, 889)
  | 11 => (173, 33, 93, 185)
  | 12 => (201, 28, 93, 185)
  | 13 => (67, 5, 25, 49)
  | 14 => (41, 62, 93, 185)
  | 15 => (852, 181, 445, 889)
  | 16 => (988, 154, 445, 889)
  | 17 => (260, 21, 93, 185)
  | 18 => (126, 48, 93, 185)
  | 19 => (100, 51, 93, 185)
  | 20 => (74, 3, 21, 41)
  | 21 => (1020, 149, 445, 889)
  | 22 => (157, 43, 93, 185)
  | 23 => (1346, 95, 445, 889)
  | 24 => (78, 56, 93, 185)
  | 25 => (241, 23, 93, 185)
  | 26 => (863, 180, 445, 889)
  | _ => (0, 0, 0, 0)

private def valid (r : Nat) : Prop :=
  let (w, n, a, b) := witness r
  w % 27 = r ∧ BB429.run n (0,w) = some (a,b) ∧
    BB429.next (a,b) = none

/-- Every second-counter residue class modulo 27 has a genuinely halting
    synthetic start with fixed first counter zero. -/
theorem every_mod27_synthetic_halt (r : Nat) (hr : r < 27) :
    ∃ w n a b, w%27=r ∧ BB429.run n (0,w)=some (a,b) ∧
      BB429.next (a,b)=none := by
  have hclasses : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 ∨ r=9 ∨ r=10 ∨ r=11 ∨ r=12 ∨ r=13 ∨ r=14 ∨ r=15 ∨ r=16 ∨ r=17 ∨ r=18 ∨ r=19 ∨ r=20 ∨ r=21 ∨ r=22 ∨ r=23 ∨ r=24 ∨ r=25 ∨ r=26 := by omega
  rcases hclasses with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26
  · subst r
    exact ⟨999, 153, 445, 889, by decide, by decide, by decide⟩
  · subst r
    exact ⟨190, 29, 93, 185, by decide, by decide, by decide⟩
  · subst r
    exact ⟨29, 2, 9, 17, by decide, by decide, by decide⟩
  · subst r
    exact ⟨1272, 107, 445, 889, by decide, by decide, by decide⟩
  · subst r
    exact ⟨814, 190, 445, 889, by decide, by decide, by decide⟩
  · subst r
    exact ⟨167, 4, 45, 89, by decide, by decide, by decide⟩
  · subst r
    exact ⟨60, 58, 93, 185, by decide, by decide, by decide⟩
  · subst r
    exact ⟨34, 63, 93, 185, by decide, by decide, by decide⟩
  · subst r
    exact ⟨8, 1, 3, 5, by decide, by decide, by decide⟩
  · subst r
    exact ⟨171, 41, 93, 185, by decide, by decide, by decide⟩
  · subst r
    exact ⟨982, 158, 445, 889, by decide, by decide, by decide⟩
  · subst r
    exact ⟨173, 33, 93, 185, by decide, by decide, by decide⟩
  · subst r
    exact ⟨201, 28, 93, 185, by decide, by decide, by decide⟩
  · subst r
    exact ⟨67, 5, 25, 49, by decide, by decide, by decide⟩
  · subst r
    exact ⟨41, 62, 93, 185, by decide, by decide, by decide⟩
  · subst r
    exact ⟨852, 181, 445, 889, by decide, by decide, by decide⟩
  · subst r
    exact ⟨988, 154, 445, 889, by decide, by decide, by decide⟩
  · subst r
    exact ⟨260, 21, 93, 185, by decide, by decide, by decide⟩
  · subst r
    exact ⟨126, 48, 93, 185, by decide, by decide, by decide⟩
  · subst r
    exact ⟨100, 51, 93, 185, by decide, by decide, by decide⟩
  · subst r
    exact ⟨74, 3, 21, 41, by decide, by decide, by decide⟩
  · subst r
    exact ⟨1020, 149, 445, 889, by decide, by decide, by decide⟩
  · subst r
    exact ⟨157, 43, 93, 185, by decide, by decide, by decide⟩
  · subst r
    exact ⟨1346, 95, 445, 889, by decide, by decide, by decide⟩
  · subst r
    exact ⟨78, 56, 93, 185, by decide, by decide, by decide⟩
  · subst r
    exact ⟨241, 23, 93, 185, by decide, by decide, by decide⟩
  · subst r
    exact ⟨863, 180, 445, 889, by decide, by decide, by decide⟩

/-- No halt-free forward invariant periodic in the second counter modulo 27
    can contain a state with first counter zero (in particular the blank seed). -/
theorem no_vertical_mod27_nonhalting_invariant
    (P : Nat × Nat → Prop) (w : Nat)
    (hseed : P (0,w))
    (hperiod : ∀ a b c, b%27=c%27 → P (a,b) → P (a,c))
    (hstep : ∀ x y, P x → BB429.next x = some y → P y)
    (hhalt : ∀ x, P x → BB429.next x ≠ none) : False := by
  obtain ⟨W,n,a,b,hw,hr,hn⟩ := every_mod27_synthetic_halt (w%27) (Nat.mod_lt _ (by decide))
  have hp : P (0,W) := hperiod 0 w W hw.symm hseed
  have hp_run : ∀ (k : Nat) (s t : Nat × Nat), P s →
      BB429.run k s = some t → P t := by
    intro k
    induction k with
    | zero =>
        intro s t hs ht
        simp [BB429.run] at ht
        simpa [ht] using hs
    | succ k ih =>
        intro s t hs ht
        simp only [BB429.run] at ht
        cases hprev : BB429.run k s with
        | none => simp [hprev] at ht
        | some p =>
            simp only [hprev, Option.bind_some] at ht
            exact hstep p t (ih s p hs hprev) ht
  exact hhalt (a,b) (hp_run n (0,W) (a,b) hp hr) hn

#print axioms every_mod27_synthetic_halt
#print axioms no_vertical_mod27_nonhalting_invariant
end BB429Full27
