import F0Counter1LD
import F0SiblingCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent6F0.AFirst

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47WeightedHalt
open BB6.Agent6F0

def childA (f mv : Move) : PartialMachine :=
  refine (parent f) (0,true) (some mv)

theorem parent_hole_A (f : Move) : parent f (0,true) = none := rfl
theorem child_hole_B (f mv : Move) : childA f mv (1,true) = none := rfl

theorem child_rest_A (f mv : Move) (s : Slot) (hs : s ≠ (1,true)) :
    ∃ w, childA f mv s = some (some w) := by
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases b
  · exact ⟨⟨true,true,1⟩,rfl⟩
  · exact ⟨mv,rfl⟩
  · exact ⟨⟨true,true,2⟩,rfl⟩
  · exact False.elim (hs rfl)
  · exact ⟨⟨true,false,3⟩,rfl⟩
  · exact ⟨⟨false,true,5⟩,rfl⟩
  · exact ⟨⟨true,true,0⟩,rfl⟩
  · exact ⟨⟨false,false,4⟩,rfl⟩
  · exact ⟨⟨false,false,3⟩,rfl⟩
  · exact ⟨⟨true,true,2⟩,rfl⟩
  · exact ⟨f,rfl⟩
  · exact ⟨⟨false,true,4⟩,rfl⟩

theorem short_child_A (B : Nat) (f mv : Move) (n : Nat) (hn : n+6 ≤ B)
    (h : BB6.Agent48Parent.check (childA f mv) n (1,true) = true) :
    Cover (WeightedBound B) (childA f mv) := by
  obtain ⟨c,hr,hs⟩ := BB6.Agent48Parent.check_sound _ _ _ h
  apply Cover.leaf
  exact last_hole_sound B (childA f mv) n c (by rfl) hr
    (by rw [hs]; exact child_hole_B f mv)
    (by intro s hne; exact child_rest_A f mv s (by simpa [hs] using hne))
    (bound hn)

theorem halt_child_A (B : Nat) (f : Move) (n : Nat) (hn : n+6 ≤ B)
    (h : BB6.Agent48Parent.check (parent f) n (0,true) = true) :
    Cover (WeightedBound B) (refine (parent f) (0,true) none) := by
  obtain ⟨c,hr,hs⟩ := BB6.Agent48Parent.check_sound _ _ _ h
  have hh := first_hole_weighted_halt B (parent f) n c (by rfl) hr
    (by rw [hs]; exact parent_hole_A f) (bound hn)
  rw [hs] at hh
  exact .leaf _ hh

theorem all_children_A (B : Nat) (f : Move) (n : Nat) (hn : n+6 ≤ B)
    (h : BB6.Agent48Parent.check (parent f) n (0,true) = true)
    (hchildren : ∀ mv, Cover (WeightedBound B) (childA f mv)) :
    Cover (WeightedBound B) (parent f) := by
  apply Cover.branch (parent f) (0,true) (parent_hole_A f)
  intro t _
  cases t with
  | none => exact halt_child_A B f n hn h
  | some mv => exact hchildren mv

theorem ordinary_oneLD (B : Nat) (hB : 707 ≤ B) (mv : Move) :
    Cover (WeightedBound B) (childA ⟨true,false,3⟩ mv) := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact side_cover B _ 0 193 false 7 (by decide) (by decide)
  · exact short_child_A B _ _ 178 (by omega) (by decide)
  · exact short_child_A B _ _ 64 (by omega) (by decide)
  · exact side_cover B _ 188 80 true 10 (by decide) (by decide)
  · exact short_child_A B _ _ 56 (by omega) (by decide)
  · exact short_child_A B _ _ 113 (by omega) (by decide)
  · exact short_child_A B _ _ 56 (by omega) (by decide)
  · exact side_cover B _ 148 23 true 10 (by decide) (by decide)
  · exact side_cover B _ 52 4 true 6 (by decide) (by decide)
  · exact side_cover B _ 54 3 true 6 (by decide) (by decide)
  · exact side_cover B _ 277 45 true 11 (by decide) (by decide)
  · exact side_cover B _ 93 88 true (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.Counter1LD.cover_oneLD_zeroLD B
  · exact short_child_A B _ _ 644 (by omega) (by decide)
  · exact side_cover B _ 409 65 true 11 (by decide) (by decide)
  · exact side_cover B _ 233 71 true 7 (by decide) (by decide)
  · exact side_cover B _ 421 67 true 11 (by decide) (by decide)
  · exact side_cover B _ 260 124 true 10 (by decide) (by decide)
  · exact side_cover B _ 52 5 true 6 (by decide) (by decide)
  · exact side_cover B _ 509 55 true 17 (by decide) (by decide)
  · exact side_cover B _ 156 27 true 10 (by decide) (by decide)
  · exact side_cover B _ 53 3 true 6 (by decide) (by decide)
  · exact short_child_A B _ _ 701 (by omega) (by decide)
  · exact side_cover B _ 459 37 true 19 (by decide) (by decide)

theorem cover_oneLD (B : Nat) (hB : 707 ≤ B) :
    Cover (WeightedBound B) (parent ⟨true,false,3⟩) :=
  all_children_A B _ 55 (by omega) (by decide) (ordinary_oneLD B hB)

#print axioms cover_oneLD
end BB6.Agent6F0.AFirst
