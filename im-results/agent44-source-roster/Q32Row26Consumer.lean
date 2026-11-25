import Q32Slice26
import RootFrontier
import Raw10BoxCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent44Q32Row26
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent44Q32Slice

abbrev parent : PartialMachine :=
  BB6Coverage.refine
    (BB6Coverage.refine BB6.Agent50TNFPilot.root
      (⟨1, by decide⟩, false)
      (some ⟨true, true, ⟨2, by decide⟩⟩))
    (⟨2, by decide⟩, false)
    (some ⟨false, false, ⟨0, by decide⟩⟩)

theorem parent_encoding :
    BB6.Agent50RootFrontier.encodeTable parent =
      "1RB---_1RC---_0LA---_------_------_------" := by decide

theorem row26_encoding :
    BB6.Agent50RootFrontier.encodeTable p26 =
      "1RB1RD_1RC0LC_0LA---_1LA0LB_------_------" := by decide

theorem row26_refines_check :
    (List.finRange 6).all (fun q =>
      [false,true].all (fun b =>
        match parent (q,b) with
        | none => true
        | some t => decide (p26 (q,b) = some t))) = true := by decide

theorem row26_refines_parent (m : Machine) (hm : compatible p26 m) :
    compatible parent m := by
  intro s t ht
  rcases s with ⟨q,b⟩
  have hq := List.all_eq_true.mp row26_refines_check q (List.mem_finRange q)
  have hb : b ∈ [false,true] := by cases b <;> simp
  have hs := List.all_eq_true.mp hq b hb
  rw [ht] at hs
  exact hm (q,b) t (of_decide_eq_true hs)

theorem row26_safe_at (B : Nat) (hB : 46 ≤ B) (m : Machine)
    (hm : compatible p26 m) : WeightedBound B m := by
  have h := safe26 m hm
  intro k d hk hd
  exact Nat.le_trans (h k d hk hd) hB

/-- Consume row26 alongside an arbitrary previously accepted roster while
    preserving every box in the exact remaining parent complement. -/
def cover_from_augmented_remainder (B : Nat) (hB : 46 ≤ B)
    (prior : List PartialMachine)
    (hPrior : ∀ p ∈ prior, ∀ m, compatible p m → WeightedBound B m)
    (hOpen : ∀ box ∈ BB6.Agent49BoxBridge.remainder parent (p26 :: prior),
      ∀ m, BB6.Agent49Box.Fits box m → WeightedBound B m) :
    Cover (WeightedBound B) parent :=
  BB6.Agent49BoxBridge.coverFromRemainder B parent (p26 :: prior)
    (fun p hp m hm => by
      rcases List.mem_cons.mp hp with h | h
      · subst p
        exact row26_safe_at B hB m hm
      · exact hPrior p h m hm) hOpen

#print axioms parent_encoding
#print axioms row26_encoding
#print axioms row26_refines_parent
#print axioms row26_safe_at
#print axioms cover_from_augmented_remainder
end BB6.Agent44Q32Row26
