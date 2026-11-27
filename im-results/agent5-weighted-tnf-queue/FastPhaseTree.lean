import PhaseTree
import PackedZipper

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent5FastPhaseTree
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
open BB6Coverage.Agent13PackedZipper
open BB6Coverage.Agent10ZipAudit
open BB6.Agent1NGram

/-- Same first-hole contract, evaluated with the already proved packed zipper. -/
def firstOK (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) : Bool :=
  decide (readRunP p n = some s) && decide (p s = none) && decide (n+6 ≤ B)

theorem firstOK_sound {B p n s} (h : firstOK B p n s = true) :
    firstHoleOK B p n s = true := by
  simpa only [firstOK, firstHoleOK, readRunP_eq, zipRead_eq] using h

/-- Identical normalized first-hole tree; faster original-source finite replays.
    The side-cycle leaf uses the independently proved padded zipper comparison. -/
def check (B : Nat) (p : PartialMachine) : Tree → Bool
  | .bad => false
  | .side e n r b => decide (0 < n) && zipCycle p e n r b
  | .automata c => BB6.Agent4Automata.check p c
  | .last n s => firstOK B p n s && BB6.Agent50TNFPilot.restOK p s
  | .split n s cut kids => firstOK B p n s && decide (0 < cut) && supportOK p cut &&
      (List.finRange 6).all (fun q => if q.val ≤ cut then bits.all (fun w => bits.all (fun r =>
        check B (refine p s (some ⟨w,r,q⟩)) (kids ⟨w,r,q⟩))) else true)

theorem sound (B : Nat) (p : PartialMachine) (t : Tree)
    (hf : p initialSlot = some (some ⟨true,true,1⟩)) (h : check B p t = true) :
    ∀ m, compatible p m → WeightedBound B m := by
  induction t generalizing p with
  | bad => simp [check] at h
  | side e n r b =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at h
    intro m hm
    exact weighted_never B m (zipCycle_sound p e n r b h.1 h.2 m hm)
  | automata c =>
    intro m hm
    exact weighted_never B m (BB6.Agent4Automata.never p c h m hm)
  | last n s =>
    simp only [check,Bool.and_eq_true] at h
    exact BB6.Agent5PhaseTree.sound B p (.last n s) hf (by
      simp only [BB6.Agent5PhaseTree.check,Bool.and_eq_true]
      exact ⟨firstOK_sound h.1,h.2⟩)
  | split n s cut kids ih =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at h
    have hh := firstOK_sound h.1.1.1
    obtain ⟨c,hr,hs,hu,hb⟩ := firstHoleOK_sound hh
    subst s
    apply split_safe B p n (readSlot c) cut hf hh h.1.1.2 h.1.2
    intro mv hv
    apply ih mv _ (refine_preserves_firstOne p _ _ hu hf)
    rcases mv with ⟨w,r,q⟩
    have H := List.all_eq_true.mp h.2 q (mem_states q)
    simp only [hv,ite_true] at H
    exact List.all_eq_true.mp (List.all_eq_true.mp H w (mem_bits w)) r (mem_bits r)

theorem splitFast (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) (cut : Nat)
    (hf : p initialSlot = some (some ⟨true,true,1⟩)) (h : firstOK B p n s = true)
    (hc : 0 < cut) (hs : supportOK p cut = true)
    (hk : ∀ mv : Move, mv.next.val ≤ cut → ∀ m,
      compatible (refine p s (some mv)) m → WeightedBound B m) :
    ∀ m, compatible p m → WeightedBound B m :=
  split_safe B p n s cut hf (firstOK_sound h) hc hs hk

/-- Long last-hole trace: composed packed runs establish the exact read slot.
    No recomputation of the long blank run in the final leaf proof. -/
theorem lastPacked (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) (z : P)
    (hr : runP p n startP = some z)
    (hs : readP z = s) (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hu : p s = none) (hrest : BB6.Agent50TNFPilot.restOK p s = true)
    (hb : n+6 ≤ B) : ∀ m, compatible p m → WeightedBound B m := by
  have hread : readRunP p n = some s := by simp [readRunP,hr,hs]
  have hh : firstOK B p n s = true := by simp [firstOK,hread,hu,hb]
  exact sound B p (.last n s) hf (by simp [check,hh,hrest])

#print axioms sound
#print axioms splitFast
#print axioms lastPacked
end BB6.Agent5FastPhaseTree
