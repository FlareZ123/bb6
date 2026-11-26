import Q0ExhaustiveTree
import SparseZipper
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Q0Trace
open BB6Coverage BB6.Agent13BlankDelay Q0ExhaustiveTree
open BB6Coverage.Agent50Zipper

def zblank : Z := ⟨0,0,[],[]⟩
theorem zblank_embed : embed zblank = blank := by
  unfold embed zblank blank
  congr 1
  funext x
  simp [atCell]

theorem last_trace (B n : Nat) (p : PartialMachine) (z : Z)
    (h : zrun p n zblank = some z)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hh : p (z.q,z.l.headD false) = none)
    (hr : allOrdExcept p (z.q,z.l.headD false) = true)
    (hb : n+6 ≤ B) : Cover (WeightedBound B) p := by
  have hz := zrun_sound p (weightedTNFDefaultCompletion p) (weightedTNFDefaultCompletion_compatible p) n zblank z h
  rw [zblank_embed,← weightedTNFKnownRun_eq_defaultRun] at hz
  have hu : p (readSlot (embed z)) = none := by rw [read_embed]; exact hh
  have hrest : ∀ t, t ≠ readSlot (embed z) → ∃ mv, p t = some (some mv) := by
    rw [read_embed]
    exact allOrdExcept_sound hr
  have hd : ∀ d ∈ possibleDelays (refine p (readSlot (embed z)) none) 0, d+n+1 ≤ B := by
    intro d hd
    have h5 := delay_le5 _ _ _ hd
    omega
  exact .leaf _ (last_hole_sound B p n (embed z) hf hz hu hrest hd)
#print axioms last_trace
end Q0Trace
