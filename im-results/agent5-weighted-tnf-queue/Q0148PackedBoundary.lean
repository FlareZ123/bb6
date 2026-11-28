import Q0148BoundarySweep
import Q0148GapInvariant

namespace BB6.Agent5Q0148PackedBoundary
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent13PackedZipper
open BB6.Agent5PackedSweep BB6.Agent5Q0148BoundarySweep BB6.Agent5Q0148GapInvariant

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Canonical head-relative chunk sequence. The leading 2 A chunks
and the following 11010 marker contain the third A via the head frame. -/
def blocks : List Nat → List LeftChunk
  | [] => []
  | u::us => List.replicate (2*u) .alternating ++ [.separatedMarker] ++ blocks us

def boundaryChunks (g : GapState) : List LeftChunk :=
  blocks (1::g.xs.reverse) ++ List.replicate (2*g.b) .alternating

def boundary (g : GapState) : P :=
  ⟨4,pack ([true,false] ++ inputBits (boundaryChunks g)),2⟩

def base : GapState := ⟨1,1,[1,1]⟩

theorem base_valid : valid base := base_good

/-- Direct original-table blank entry: includes both the exceptional
147-step first boundary and the entire 548-step next boundary epoch. -/
theorem blank695 : runP p 695 startP = some (boundary base) := by decide +kernel

theorem zero_pack (n : Nat) : pack (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,pack,ih]

theorem append_zero_pack (xs : List Bool) (n : Nat) :
    pack (xs ++ List.replicate n false) = pack xs := by
  simp [pack_append,cat,zero_pack]

/-- Arbitrarily padded exact source configurations denote the same
physical packed boundary, irrespective of their explicit zero count. -/
theorem padded_boundary (g : GapState) (l r : Nat) :
    encode0 ⟨4,[true,false] ++ inputBits (boundaryChunks g) ++ List.replicate l false,
      [false,true,false] ++ List.replicate r false⟩ = boundary g := by
  unfold encode0 boundary
  simp only [append_zero_pack]
  rfl

theorem packed_of_run0 {k : Nat} {a b : Z0} (h : run0 p k a = some b) :
    runP p k (encode0 a) = some (encode0 b) := by
  rw [← encode0_run,h]; rfl

theorem runP_prefix {a b : Nat} {x z : P} (hab : a ≤ b)
    (h : runP p b x = some z) : runP p a x ≠ none := by
  intro hn
  rw [show b = a+(b-a) by omega,runP_add,hn] at h
  contradiction

/-- Once the physical epoch correspondence is certified, the original
blank run is defined at every finite time. No exact return cost needed. -/
theorem blank_live_of_epoch
    (epoch : ∀ g, valid g → ∃ k, 0 < k ∧ runP p k (boundary g) = some (boundary (next g)))
    (n : Nat) : runP p n startP ≠ none := by
  have hv := live_of_returns (runP p) boundary (fun h g => joinP h g)
    (fun ha h => runP_prefix ha h) epoch base base_valid n
  cases h : runP p n (boundary base) with
  | none => exact False.elim (hv h)
  | some z => exact runP_prefix (by omega) (joinP blank695 h)

/-- The packed partial-table run uses the exact original zipper semantics,
so every total completion of the F1 hole is nonhalting. -/
theorem completion_live_of_epoch
    (epoch : ∀ g, valid g → ∃ k, 0 < k ∧ runP p k (boundary g) = some (boundary (next g)))
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  intro n
  have h := blank_live_of_epoch epoch n
  have hencode := encode_run p n BB6Coverage.Agent31Pump.start
  rw [show encode BB6Coverage.Agent31Pump.start = startP from rfl] at hencode
  cases hz : BB6Coverage.Agent50Zipper.zrun p n BB6Coverage.Agent31Pump.start with
  | none => simp [hz] at hencode; exact False.elim (h hencode.symm)
  | some z =>
    have hs := BB6Coverage.Agent50Zipper.zrun_sound p m hm n _ _ hz
    rw [BB6Coverage.Agent31Pump.start_embed] at hs
    change (run m n blank).isSome = true
    rw [hs]; rfl

theorem cover_of_epoch
    (epoch : ∀ g, valid g → ∃ k, 0 < k ∧ runP p k (boundary g) = some (boundary (next g))) :
    Cover NeverHalts p := .leaf p (completion_live_of_epoch epoch)

#print axioms blank695
#print axioms padded_boundary
#print axioms packed_of_run0
#print axioms blank_live_of_epoch
#print axioms cover_of_epoch
end BB6.Agent5Q0148PackedBoundary
