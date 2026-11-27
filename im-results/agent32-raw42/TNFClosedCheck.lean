import PartialCut
import Raw59QuickWeight
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Closed
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent32PartialCut BB6.Agent32Raw59QuickWeight

def quickLeaf (B : Nat) (p : PartialMachine) : Audit → Bool
  | .last n s => quickZipQuery B p n s && restOK p s
  | a => zipCheck B p a

theorem quickLeaf_eq (B : Nat) (p : PartialMachine) (a : Audit) : quickLeaf B p a = zipCheck B p a := by
  cases a <;> simp only [quickLeaf,quickZipQuery_eq,zipCheck]

def closedCheck (B cut : Nat) (p : PartialMachine) : Cut → Bool
  | .keep => false
  | .closed a => quickLeaf B p a
  | .split n s kids => quickZipQuery B p n s && allMoves (fun mv =>
      if mv.next.val ≤ cut then closedCheck B (advanceCut cut mv) (refine p s (some mv)) (kids mv) else true)
termination_by structural t => t

theorem closedCover (B cut : Nat) (p : PartialMachine) (t : Cut)
    (hcut : 0 < cut) (hs : TNFSupport p cut)
    (hr : p initialSlot = some (some ⟨true,true,1⟩))
    (hn : weightedTNFNoAssignedHalt p)
    (hc : closedCheck B cut p t = true) :
    Cover (WeightedBound B) p := by
  induction t generalizing p cut with
  | keep => simp [closedCheck] at hc
  | closed a => exact .leaf p ((certifiedZip B p a hr hn (by simpa only [closedCheck,quickLeaf_eq] using hc)).sound)
  | split n s kids ih =>
    have hh : quickZipQuery B p n s = true ∧ allMoves (fun mv =>
        if mv.next.val ≤ cut then closedCheck B (advanceCut cut mv)
          (refine p s (some mv)) (kids mv) else true) = true := by
      simpa only [closedCheck,Bool.and_eq_true] using hc
    have hq : zipQueryOK B p n s = true := by simpa only [quickZipQuery_eq] using hh.1
    obtain ⟨hread,hu,_⟩ := zipQueryOK_sound hq
    have hslot : s.1.val < cut := by
      cases hk : knownRun p n with
      | none => simp [hk] at hread
      | some c =>
        have he : readSlot c = s := by simpa [hk] using hread
        rw [← he]
        exact knownRun_support p cut hcut hs n c hk
    have hchild : ∀ mv : Move, mv.next.val ≤ cut →
        Cover (WeightedBound B) (refine p s (some mv)) := by
      intro mv hm
      have hc' : closedCheck B (advanceCut cut mv) (refine p s (some mv)) (kids mv) = true := by
        simpa only [if_pos hm] using allMoves_sound _ hh.2 mv
      have hg : cut ≤ advanceCut cut mv := by unfold advanceCut; split <;> omega
      have hmv : mv.next.val < advanceCut cut mv := by unfold advanceCut; split <;> omega
      have hs' := refine_support p s mv cut (advanceCut cut mv) hs hg (by omega) hmv
      apply ih mv (advanceCut cut mv) (refine p s (some mv)) (by omega) hs'
        (refine_preserves_firstOne p s (some mv) hu hr)
        (weightedTNFNoAssignedHalt_refine p s mv hn) hc'
    exact .leaf p (tnf_branch_sound B cut p s hcut hs hu hslot hr
      (haltAtQuery B p n s hr hq)
      (fun mv hm => (hchild mv (by omega)).sound)
      (fun q hq w r => (hchild ⟨w,r,q⟩ (by simp [hq])).sound))

theorem split_checked (B cut : Nat) (p : PartialMachine) (n : Nat) (s : Slot) (kids : Move → Cut)
    (hq : quickZipQuery B p n s = true)
    (hk : ∀ mv, (if mv.next.val ≤ cut then closedCheck B (advanceCut cut mv) (refine p s (some mv)) (kids mv) else true) = true) :
    closedCheck B cut p (.split n s kids) = true := by
  simp only [closedCheck,hq,Bool.true_and]
  exact allMoves_of _ hk
#print axioms closedCover
end BB6.Agent32Closed
