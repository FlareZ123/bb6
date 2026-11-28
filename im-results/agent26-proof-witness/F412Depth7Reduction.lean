import F412Depth8Reduction
import F412Depth7Case00
import F412Depth7Case01
import F412Depth7Case02
import F412Depth7Case03
import F412Depth7Case04
import F412Depth7Case05
import F412Depth7Case06
import F412Depth7Case07
import F412Depth7Case08
import F412Depth7Case09
import F412Depth7Case10
import F412Depth7Case11
import F412Depth7Case12

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent26F412Depth7
open BB6Coverage BB6.Agent26F412Graft BB6.Agent26F412NGram
open BB6.Agent26F412Depth8 BB6.Agent26F412TwoHole

/-- The actual thirteen unresolved depth-seven F0 siblings. -/
def fDepth7Siblings : List (Fin 9 × Move) := [
  (⟨7, by decide⟩, ⟨false,false,1⟩),
  (⟨7, by decide⟩, ⟨false,false,2⟩),
  (⟨7, by decide⟩, ⟨false,false,3⟩),
  (⟨7, by decide⟩, ⟨false,false,4⟩),
  (⟨7, by decide⟩, ⟨false,false,5⟩),
  (⟨7, by decide⟩, ⟨false,true,0⟩),
  (⟨7, by decide⟩, ⟨false,true,1⟩),
  (⟨7, by decide⟩, ⟨true,false,0⟩),
  (⟨7, by decide⟩, ⟨true,false,1⟩),
  (⟨7, by decide⟩, ⟨true,false,2⟩),
  (⟨7, by decide⟩, ⟨true,false,4⟩),
  (⟨7, by decide⟩, ⟨true,true,0⟩),
  (⟨7, by decide⟩, ⟨true,true,1⟩)
]

theorem fDepth7Siblings_length : fDepth7Siblings.length = 13 := by decide
theorem fDepth7Siblings_nodup : fDepth7Siblings.Nodup := by decide
theorem fDepth7Siblings_in_remaining140 :
    ∀ e ∈ fDepth7Siblings, e ∈ fRemaining140 := by decide

/-- All 13 cylinders, including every ordinary and halting completion of
    each, have a source-checkable weighted bound from 312 children. None
    of these arguments requires F412's enormous exact primitive clock. -/
theorem fDepth7Siblings_weighted (B : Nat) (hB : 128 ≤ B)
    (e : Fin 9 × Move) (he : e ∈ fDepth7Siblings)
    (m : Machine) (hm : compatible (fChild e.1 e.2) m) : WeightedBound B m := by
  have cases :
      e = (⟨7, by decide⟩, ⟨false,false,1⟩) ∨
      e = (⟨7, by decide⟩, ⟨false,false,2⟩) ∨
      e = (⟨7, by decide⟩, ⟨false,false,3⟩) ∨
      e = (⟨7, by decide⟩, ⟨false,false,4⟩) ∨
      e = (⟨7, by decide⟩, ⟨false,false,5⟩) ∨
      e = (⟨7, by decide⟩, ⟨false,true,0⟩) ∨
      e = (⟨7, by decide⟩, ⟨false,true,1⟩) ∨
      e = (⟨7, by decide⟩, ⟨true,false,0⟩) ∨
      e = (⟨7, by decide⟩, ⟨true,false,1⟩) ∨
      e = (⟨7, by decide⟩, ⟨true,false,2⟩) ∨
      e = (⟨7, by decide⟩, ⟨true,false,4⟩) ∨
      e = (⟨7, by decide⟩, ⟨true,true,0⟩) ∨
      e = (⟨7, by decide⟩, ⟨true,true,1⟩) := by
    simpa [fDepth7Siblings] using he
  rcases cases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
  · subst e
    exact Case00.parent_sound B hB m (by simpa [Case00.fm, pF0] using hm)
  · subst e
    exact Case01.parent_sound B hB m (by simpa [Case01.fm, pF0] using hm)
  · subst e
    exact Case02.parent_sound B hB m (by simpa [Case02.fm, pF0] using hm)
  · subst e
    exact Case03.parent_sound B hB m (by simpa [Case03.fm, pF0] using hm)
  · subst e
    exact Case04.parent_sound B hB m (by simpa [Case04.fm, pF0] using hm)
  · subst e
    exact Case05.parent_sound B hB m (by simpa [Case05.fm, pF0] using hm)
  · subst e
    exact Case06.parent_sound B hB m (by simpa [Case06.fm, pF0] using hm)
  · subst e
    exact Case07.parent_sound B hB m (by simpa [Case07.fm, pF0] using hm)
  · subst e
    exact Case08.parent_sound B hB m (by simpa [Case08.fm, pF0] using hm)
  · subst e
    exact Case09.parent_sound B hB m (by simpa [Case09.fm, pF0] using hm)
  · subst e
    exact Case10.parent_sound B hB m (by simpa [Case10.fm, pF0] using hm)
  · subst e
    exact Case11.parent_sound B hB m (by simpa [Case11.fm, pF0] using hm)
  · subst e
    exact Case12.parent_sound B hB m (by simpa [Case12.fm, pF0] using hm)

/-- Actual 140-13=127 complement, accounting for 59 previous loop
    certificates, 9 original early-halters, 4 new N-grams, 4 final
    depth-eight halt leaves, and all 13 depth-seven parents. -/
def fRemaining127 : List (Fin 9 × Move) :=
  fRemaining140.filter (fun e => !(decide (e ∈ fDepth7Siblings)))

theorem fRemaining127_length : fRemaining127.length = 127 := by decide
theorem fRemaining127_no_depth7_or8 :
    ∀ e ∈ fRemaining127, e.1.val ≠ 7 ∧ e.1.val ≠ 8 := by decide

def FDisposition127 (B : Nat) (m : Machine) : Prop :=
  WeightedBound B m ∨
  ∃ e ∈ fRemaining127, compatible (fChild e.1 e.2) m

theorem fResidualSound127 (B : Nat) (hB : fMoves+1 ≤ B)
    (hclock : HaltsAfter fLiteral fMoves) :
    ∀ m, compatible fResidual m → FDisposition127 B m := by
  have h128 : 128 ≤ B := by unfold fMoves at hB; omega
  intro m hm
  rcases fResidualSound140 B hB hclock m hm with hb | ⟨e,he,hc⟩
  · exact Or.inl hb
  · by_cases hnew : e ∈ fDepth7Siblings
    · exact Or.inl (fDepth7Siblings_weighted B h128 e hnew m hc)
    · refine Or.inr ⟨e, ?_, hc⟩
      simp [fRemaining127, he, hnew]

#print axioms fDepth7Siblings_weighted
#print axioms fRemaining127_length
#print axioms fRemaining127_no_depth7_or8
#print axioms fResidualSound127

end BB6.Agent26F412Depth7
