import ChampionParentCover
import FastFAR

/-! Independent complete depth-six F0 sibling covers. -/
namespace BB6.Agent6F0
open BB6Coverage BB6.Agent13BlankDelay BB6Coverage.Agent50SideCycle
open BB6.Agent47WeightedHalt

def base : PartialMachine := FAR.fromCodes [7,24,11,24,14,21,3,16,12,11,24,17]
def parent (f : Move) : PartialMachine := refine base (5,false) (some f)
def child (f mv : Move) : PartialMachine := refine (parent f) (1,true) (some mv)

theorem parent_hole (f : Move) : parent f (1,true) = none := rfl
theorem child_hole (f mv : Move) : child f mv (0,true) = none := rfl

theorem child_rest (f mv : Move) (s : Slot) (hs : s ≠ (0,true)) :
    ∃ w, child f mv s = some (some w) := by
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases b
  · exact ⟨⟨true,true,1⟩,rfl⟩
  · exact False.elim (hs rfl)
  · exact ⟨⟨true,true,2⟩,rfl⟩
  · exact ⟨mv,rfl⟩
  · exact ⟨⟨true,false,3⟩,rfl⟩
  · exact ⟨⟨false,true,5⟩,rfl⟩
  · exact ⟨⟨true,true,0⟩,rfl⟩
  · exact ⟨⟨false,false,4⟩,rfl⟩
  · exact ⟨⟨false,false,3⟩,rfl⟩
  · exact ⟨⟨true,true,2⟩,rfl⟩
  · exact ⟨f,rfl⟩
  · exact ⟨⟨false,true,4⟩,rfl⟩

theorem bound {B n : Nat} {p : PartialMachine} (hB : n+6 ≤ B) :
    ∀ d ∈ possibleDelays p 0, d+n+1 ≤ B := by
  intro d hd
  unfold possibleDelays at hd
  have hd' := List.mem_range.mp (List.mem_filter.mp hd).1
  omega

theorem short_child (B : Nat) (f mv : Move) (n : Nat) (hn : n+6 ≤ B)
    (h : BB6.Agent48Parent.check (child f mv) n (0,true) = true) :
    Cover (WeightedBound B) (child f mv) := by
  obtain ⟨c,hr,hs⟩ := BB6.Agent48Parent.check_sound _ _ _ h
  apply Cover.leaf
  exact last_hole_sound B (child f mv) n c (by rfl) hr
    (by rw [hs]; exact child_hole f mv)
    (by intro s hne; exact child_rest f mv s (by simpa [hs] using hne))
    (bound hn)

theorem halt_child (B : Nat) (f : Move) (n : Nat) (hn : n+6 ≤ B)
    (h : BB6.Agent48Parent.check (parent f) n (1,true) = true) :
    Cover (WeightedBound B) (refine (parent f) (1,true) none) := by
  obtain ⟨c,hr,hs⟩ := BB6.Agent48Parent.check_sound _ _ _ h
  have hh := first_hole_weighted_halt B (parent f) n c (by rfl) hr
    (by rw [hs]; exact parent_hole f) (bound hn)
  rw [hs] at hh
  exact .leaf _ hh

theorem all_children (B : Nat) (f : Move) (n : Nat) (hn : n+6 ≤ B)
    (h : BB6.Agent48Parent.check (parent f) n (1,true) = true)
    (hchildren : ∀ mv, Cover (WeightedBound B) (child f mv)) :
    Cover (WeightedBound B) (parent f) := by
  apply Cover.branch (parent f) (1,true) (parent_hole f)
  intro t _
  cases t with
  | none => exact halt_child B f n hn h
  | some mv => exact hchildren mv

theorem far_child (B : Nat) (f mv : Move) (C : FAR.Data 2)
    (h : C.fastValid (child f mv) = true) :
    Cover (WeightedBound B) (child f mv) :=
  .leaf _ (fun m hm => weighted_never B m (C.sound _ (C.fastValid_sound _ h) m hm))

theorem side_cover (B : Nat) (p : PartialMachine) (entry period : Nat)
    (right : Bool) (boundary : Int) (hn : 0 < period)
    (h : fastSideCycleCheck p entry period right boundary = true) :
    Cover (WeightedBound B) p :=
  .leaf _ (fun m hm => weighted_never B m
    (fastSideCycleCheck_sound p entry period right boundary hn h m hm))

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ordinary_oneLA (B : Nat) (hB : 201 ≤ B) (mv : Move) :
    Cover (WeightedBound B) (child ⟨true, false, 0⟩ mv) := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact short_child B _ _ 56 (by omega) (by decide)
  · exact short_child B _ _ 117 (by omega) (by decide)
  · exact short_child B _ _ 56 (by omega) (by decide)
  · exact short_child B _ _ 195 (by omega) (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,432,128,256,432,64,432,4096,4096], [4096,432,32,432,256,16,4096,432,32,432,256,16,4096], 6148⟩ (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,2,128,256,306,64,434,4096,4096], [4096,2,32,434,256,16,4096,2,32,306,256,16,4096], 6148⟩ (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,304,128,256,304,64,432,4096,4096], [4096,32,32,432,256,16,4096,304,32,304,256,16,4096], 6148⟩ (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,128,128,256,432,64,432,4096,4096], [4096,128,32,432,256,16,4096,128,32,432,256,16,4096], 6148⟩ (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,0,128,256,304,64,432,4096,4096], [4096,4528,32,432,256,16,4096,0,32,304,256,16,4096], 6148⟩ (by decide)
  · exact short_child B _ _ 58 (by omega) (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,16,128,256,304,64,432,4096,4096], [4096,4400,32,432,256,16,4096,16,32,304,256,16,4096], 6148⟩ (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,256,128,256,304,64,432,4096,4096], [4096,256,32,432,256,16,4096,256,32,304,256,16,4096], 6148⟩ (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,432,128,256,432,64,432,4096,4096], [4096,128,32,432,256,16,4096,432,32,432,256,16,4096], 6148⟩ (by decide)
  · exact short_child B _ _ 148 (by omega) (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,304,128,256,304,64,432,4096,4096], [4096,4096,32,432,256,16,4096,304,32,304,256,16,4096], 6148⟩ (by decide)
  · exact side_cover B _ 233 71 true 7 (by decide) (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,304,128,256,304,64,432,4096,4096], [4096,432,32,432,256,16,4096,304,32,304,256,16,4096], 6148⟩ (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,16,128,256,304,64,432,4096,4096], [4096,16,32,432,256,16,4096,16,32,304,256,16,4096], 6148⟩ (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,32,128,256,304,64,432,4096,4096], [4096,304,32,432,256,16,4096,32,32,304,256,16,4096], 6148⟩ (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,1024,128,256,1328,64,1456,4096,4096], [4096,1024,32,1456,256,16,4096,1024,32,1328,256,16,4096], 6148⟩ (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,128,128,256,432,64,432,4096,4096], [4096,4352,32,432,256,16,4096,128,32,432,256,16,4096], 6148⟩ (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,32,128,256,304,64,432,4096,4096], [4096,32,32,432,256,16,4096,32,32,304,256,16,4096], 6148⟩ (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,256,128,256,304,64,432,4096,4096], [4096,4128,32,432,256,16,4096,256,32,304,256,16,4096], 6148⟩ (by decide)
  · exact short_child B _ _ 57 (by omega) (by decide)

theorem cover_oneLA (B : Nat) (hB : 201 ≤ B) :
    Cover (WeightedBound B) (parent ⟨true, false, 0⟩) :=
  all_children B _ 55 (by omega) (by decide) (ordinary_oneLA B hB)
#print axioms cover_oneLA

theorem ordinary_oneLE (B : Nat) (hB : 279 ≤ B) (mv : Move) :
    Cover (WeightedBound B) (child ⟨true, false, 4⟩ mv) := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact short_child B _ _ 98 (by omega) (by decide)
  · exact short_child B _ _ 273 (by omega) (by decide)
  · exact short_child B _ _ 98 (by omega) (by decide)
  · exact side_cover B _ 469 79 true 11 (by decide) (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,432,128,256,432,64,432,32,4096], [4096,432,32,432,256,16,4096,432,32,432,256,16,4096], 4100⟩ (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,306,128,256,306,64,434,32,4096], [4096,2,32,434,256,16,4096,2,32,306,256,16,4096], 4100⟩ (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,304,128,256,304,64,432,32,4096], [4096,32,32,432,256,16,4096,304,32,304,256,16,4096], 4100⟩ (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,432,128,256,432,64,432,32,4096], [4096,128,32,432,256,16,4096,128,32,432,256,16,4096], 4100⟩ (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,304,128,256,304,64,432,32,4096], [4096,4528,32,432,256,16,4096,304,32,304,256,16,4096], 4100⟩ (by decide)
  · exact short_child B _ _ 100 (by omega) (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,304,128,256,304,64,432,32,4096], [4096,4400,32,432,256,16,4096,16,32,304,256,16,4096], 4100⟩ (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,304,128,256,304,64,432,32,4096], [4096,256,32,432,256,16,4096,256,32,304,256,16,4096], 4100⟩ (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,432,128,256,432,64,432,32,4096], [4096,128,32,432,256,16,4096,432,32,432,256,16,4096], 4100⟩ (by decide)
  · exact side_cover B _ 678 79 true 10 (by decide) (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,304,128,256,304,64,432,32,4096], [4096,4096,32,432,256,16,4096,304,32,304,256,16,4096], 4100⟩ (by decide)
  · exact side_cover B _ 376 79 true 8 (by decide) (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,304,128,256,304,64,432,32,4096], [4096,432,32,432,256,16,4096,304,32,304,256,16,4096], 4100⟩ (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,304,128,256,304,64,432,32,4096], [4096,16,32,432,256,16,4096,16,32,304,256,16,4096], 4100⟩ (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,304,128,256,304,64,432,32,4096], [4096,304,32,432,256,16,4096,32,32,304,256,16,4096], 4100⟩ (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,1328,128,256,1328,64,1456,32,4096], [4096,1024,32,1456,256,16,4096,1024,32,1328,256,16,4096], 4100⟩ (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,432,128,256,432,64,432,32,4096], [4096,432,32,432,256,16,4096,128,32,432,256,16,4096], 4100⟩ (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,304,128,256,304,64,432,32,4096], [4096,32,32,432,256,16,4096,32,32,304,256,16,4096], 4100⟩ (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,304,128,256,304,64,432,32,4096], [4096,304,32,432,256,16,4096,256,32,304,256,16,4096], 4100⟩ (by decide)
  · exact far_child B _ _ ⟨0, [0,1,0,1], [128,256,4096,64,128,2352,128,256,2352,64,2480,32,4096], [4096,2048,32,2480,256,16,4096,2048,32,2352,256,16,4096], 4100⟩ (by decide)

theorem cover_oneLE (B : Nat) (hB : 279 ≤ B) :
    Cover (WeightedBound B) (parent ⟨true, false, 4⟩) :=
  all_children B _ 97 (by omega) (by decide) (ordinary_oneLE B hB)
#print axioms cover_oneLE

theorem cover_zeroLB (B : Nat) : Cover (WeightedBound B) (parent ⟨false, false, 1⟩) :=
  side_cover B _ 409 65 true 11 (by decide) (by decide)
#print axioms cover_zeroLB

theorem cover_oneLC (B : Nat) : Cover (WeightedBound B) (parent ⟨true, false, 2⟩) :=
  side_cover B _ 385 61 true 11 (by decide) (by decide)
#print axioms cover_oneLC

end BB6.Agent6F0
