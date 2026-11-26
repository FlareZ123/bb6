import PhaseTree
import SparseZipper
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent5PhaseFastHole
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
open BB6Coverage.Agent50Zipper
def zblank : Z := ⟨0,0,[],[]⟩
theorem zblank_embed : embed zblank = blank := by
  unfold embed zblank blank
  congr 1
  funext x
  simp [atCell]
def fastHoleOK (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) : Bool :=
  decide ((zrun p n zblank).map (fun z => (z.q,z.l.headD false)) = some s) &&
  decide (p s = none) && decide (n+6 ≤ B)
theorem fastHoleOK_sound {B p n s} (h : fastHoleOK B p n s = true) :
    ∃ c, knownRun p n = some c ∧ readSlot c = s ∧ p s = none ∧ n+6 ≤ B := by
  simp only [fastHoleOK,Bool.and_eq_true,decide_eq_true_eq] at h
  cases hz : zrun p n zblank with
  | none => simp [hz] at h
  | some z =>
    have hs : (z.q,z.l.headD false) = s := by simpa [hz] using h.1.1
    have hr := zrun_sound p (weightedTNFDefaultCompletion p) (weightedTNFDefaultCompletion_compatible p) n zblank z hz
    rw [zblank_embed,← weightedTNFKnownRun_eq_defaultRun] at hr
    exact ⟨embed z,hr,(read_embed z).trans hs,h.1.2,h.2⟩
theorem last_safe (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot)
    (hf : p initialSlot = some (some ⟨true,true,1⟩)) (h : fastHoleOK B p n s = true)
    (hr : BB6.Agent50TNFPilot.restOK p s = true) :
    ∀ m, compatible p m → WeightedBound B m := by
  obtain ⟨c,hc,hs,hu,hb⟩ := fastHoleOK_sound h
  subst s
  exact last_hole_sound B p n c hf hc hu (BB6.Agent50TNFPilot.restOK_sound _ _ hr) (delay_margin hb)
theorem fast_split_safe (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) (cut : Nat)
    (hf : p initialSlot = some (some ⟨true,true,1⟩)) (h : fastHoleOK B p n s = true)
    (hc : 0 < cut) (hs : supportOK p cut = true)
    (hk : ∀ mv : Move, mv.next.val ≤ cut → ∀ m,
      compatible (refine p s (some mv)) m → WeightedBound B m) :
    ∀ m, compatible p m → WeightedBound B m := by
  obtain ⟨c,hr,hrslot,hu,hb⟩ := fastHoleOK_sound h
  subst s
  exact tnf_branch_sound B cut p (readSlot c) hc (supportOK_sound hs) hu
    (knownRun_support p cut hc (supportOK_sound hs) n c hr) hf
    (first_hole_weighted_halt B p n c hf hr hu (delay_margin hb))
    (fun mv hv => hk mv (Nat.le_of_lt hv)) (fun q hq w r => hk ⟨w,r,q⟩ (Nat.le_of_eq hq))
#print axioms fast_split_safe
#print axioms last_safe
end BB6.Agent5PhaseFastHole
