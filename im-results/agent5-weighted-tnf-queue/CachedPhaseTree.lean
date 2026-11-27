import FastPhaseTree
import CachedZipAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent5CachedPhaseTree
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
open BB6Coverage.Agent50Zipper BB6Coverage.Agent10ZipAudit BB6Coverage.Agent13PackedZipper
open BB6.Agent10CachedAudit BB6.Agent1NGram

def query (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) (z : Z) : Bool :=
  decide ((z.q,z.l.headD false) = s) && decide (p s = none) && decide (n+6 ≤ B)

theorem query_eq (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) (z : Z)
    (hz : zrun p n start = some z) :
    query B p n s z = BB6.Agent5FastPhaseTree.firstOK B p n s := by
  simp [query,BB6.Agent5FastPhaseTree.firstOK,readRunP_eq,zipRead,hz]

/-- Share the exact execution prefix at every first-hole branch. -/
def check (B : Nat) (p : PartialMachine) (c : Cursor) : (t : Tree) → Bool
  | .bad => false
  | .side e n r b => decide (0 < n) && cycleAt p c e n r b
  | .automata a => BB6.Agent4Automata.check p a
  | .last n s =>
    match runAt p c n with
    | none => false
    | some z => query B p n s z && BB6.Agent50TNFPilot.restOK p s
  | .split n s cut kids =>
    match runAt p c n with
    | none => false
    | some z =>
      query B p n s z && decide (0 < cut) && supportOK p cut &&
      (List.finRange 6).all (fun q => if q.val ≤ cut then bits.all (fun w => bits.all (fun r =>
        check B (refine p s (some ⟨w,r,q⟩)) ⟨n,z⟩ (kids ⟨w,r,q⟩))) else true)
termination_by structural t => t

theorem check_eq (B : Nat) (p : PartialMachine) (c : Cursor) (t : Tree)
    (hc : c.Valid p) : check B p c t = BB6.Agent5FastPhaseTree.check B p t := by
  induction t generalizing p c with
  | bad => rfl
  | side e n r b => simp only [check,BB6.Agent5FastPhaseTree.check,cycleAt_eq _ _ _ _ _ _ hc]
  | automata a => rfl
  | last n s =>
    simp only [check,BB6.Agent5FastPhaseTree.check,runAt_eq _ _ _ hc]
    cases hz : zrun p n start with
    | none => simp [BB6.Agent5FastPhaseTree.firstOK,readRunP_eq,zipRead,hz]
    | some z => rw [query_eq B p n s z hz]
  | split n s cut kids ih =>
    simp only [check,BB6.Agent5FastPhaseTree.check,runAt_eq _ _ _ hc]
    cases hz : zrun p n start with
    | none => simp [BB6.Agent5FastPhaseTree.firstOK,readRunP_eq,zipRead,hz]
    | some z =>
      rw [query_eq B p n s z hz]
      cases hq : BB6.Agent5FastPhaseTree.firstOK B p n s with
      | false => simp
      | true =>
        have hh : p s = none := by
          simp only [BB6.Agent5FastPhaseTree.firstOK,Bool.and_eq_true,decide_eq_true_eq] at hq
          exact hq.1.2
        have he (mv : Move) :
            check B (refine p s (some mv)) ⟨n,z⟩ (kids mv) =
            BB6.Agent5FastPhaseTree.check B (refine p s (some mv)) (kids mv) :=
          ih mv _ _ (run_refine_hole hh (some mv) n start z hz)
        simp only [he]

def rootCheck (B : Nat) (p : PartialMachine) (t : Tree) : Bool :=
  check B p rootCursor t

theorem sound (B : Nat) (p : PartialMachine) (t : Tree)
    (hf : p initialSlot = some (some ⟨true,true,1⟩)) (h : rootCheck B p t = true) :
    ∀ m, compatible p m → WeightedBound B m :=
  BB6.Agent5FastPhaseTree.sound B p t hf (by
    unfold rootCheck at h
    rw [check_eq B p rootCursor t rfl] at h
    exact h)

#print axioms check_eq
#print axioms sound
end BB6.Agent5CachedPhaseTree
