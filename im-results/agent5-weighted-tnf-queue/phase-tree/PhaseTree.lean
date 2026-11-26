import WeightedTNFCertificate
import SideCycle
import TNFPilot
import TwoSidedAutomata

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent5PhaseTree
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent1NGram
open BB6Coverage.Agent50SideCycle (fastSideCycleCheck fastSideCycleCheck_sound)

def supportOK (p : PartialMachine) (cut : Nat) : Bool :=
  (List.finRange 6).all fun q => bits.all fun b =>
    match p (q,b) with
    | none => true
    | some none => decide (q.val < cut)
    | some (some mv) => decide (q.val < cut) && decide (mv.next.val < cut)

theorem supportOK_sound {p cut} (h : supportOK p cut = true) : TNFSupport p cut := by
  rintro ⟨q,b⟩ t ht
  have H := List.all_eq_true.mp (List.all_eq_true.mp h q (mem_states q)) b (mem_bits b)
  change (match p (q,b) with | none => true | some none => decide (q.val < cut) | some (some mv) => decide (q.val < cut) && decide (mv.next.val < cut)) = true at H
  rw [ht] at H
  cases t with
  | none => exact ⟨of_decide_eq_true H, by simp⟩
  | some mv =>
    simp only [Bool.and_eq_true,decide_eq_true_eq] at H
    exact ⟨H.1, fun v hv => Option.some.inj hv ▸ H.2⟩

def firstHoleOK (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) : Bool :=
  decide ((knownRun p n).map readSlot = some s) && decide (p s = none) && decide (n+6 ≤ B)

theorem firstHoleOK_sound {B p n s} (h : firstHoleOK B p n s = true) :
    ∃ c, knownRun p n = some c ∧ readSlot c = s ∧ p s = none ∧ n+6 ≤ B := by
  simp only [firstHoleOK,Bool.and_eq_true,decide_eq_true_eq] at h
  cases hr : knownRun p n with
  | none => simp [hr] at h
  | some c => exact ⟨c,rfl,Option.some.inj (by simpa [hr] using h.1.1),h.1.2,h.2⟩

theorem delay_margin {B n : Nat} {p : PartialMachine} (h : n+6 ≤ B) :
    ∀ d ∈ possibleDelays p 0, d+n+1 ≤ B := by
  intro d hd
  have hd' := List.mem_range.mp (List.mem_filter.mp hd).1
  omega

inductive Tree where
  | bad
  | side (entry period : Nat) (right : Bool) (boundary : Int)
  | automata (cert : BB6.Agent4Automata.Cert)
  | last (n : Nat) (s : Slot)
  | split (n : Nat) (s : Slot) (cut : Nat) (kids : Move → Tree)

def check (B : Nat) (p : PartialMachine) : Tree → Bool
  | .bad => false
  | .side e n r b => decide (0 < n) && fastSideCycleCheck p e n r b
  | .automata c => BB6.Agent4Automata.check p c
  | .last n s => firstHoleOK B p n s && BB6.Agent50TNFPilot.restOK p s
  | .split n s cut kids => firstHoleOK B p n s && decide (0 < cut) && supportOK p cut &&
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
    exact weighted_never B m (fastSideCycleCheck_sound p e n r b h.1 h.2 m hm)
  | automata c =>
    intro m hm
    exact weighted_never B m (BB6.Agent4Automata.never p c h m hm)
  | last n s =>
    simp only [check,Bool.and_eq_true] at h
    obtain ⟨c,hr,hs,hu,hb⟩ := firstHoleOK_sound h.1
    subst s
    exact last_hole_sound B p n c hf hr hu (BB6.Agent50TNFPilot.restOK_sound _ _ h.2) (delay_margin hb)
  | split n s cut kids ih =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨c,hr,hs,hu,hb⟩ := firstHoleOK_sound h.1.1.1
    subst s
    have hc := h.1.1.2
    have hsupport := supportOK_sound h.1.2
    have hslot : (readSlot c).1.val < cut := knownRun_support p cut hc hsupport n c hr
    have getChild (mv : Move) (hv : mv.next.val ≤ cut) :
        ∀ m, compatible (refine p (readSlot c) (some mv)) m → WeightedBound B m := by
      apply ih mv _ (refine_preserves_firstOne p _ _ hu hf)
      rcases mv with ⟨w,r,q⟩
      have H := List.all_eq_true.mp h.2 q (mem_states q)
      simp only [hv,ite_true] at H
      exact List.all_eq_true.mp (List.all_eq_true.mp H w (mem_bits w)) r (mem_bits r)
    exact tnf_branch_sound B cut p (readSlot c) hc hsupport hslot hf
      (first_hole_weighted_halt B p n c hf hr hu (delay_margin hb))
      (fun mv hv => getChild mv (Nat.le_of_lt hv))
      (fun q hq w r => getChild ⟨w,r,q⟩ (Nat.le_of_eq hq))

theorem split_safe (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) (cut : Nat)
    (hf : p initialSlot = some (some ⟨true,true,1⟩)) (h : firstHoleOK B p n s = true)
    (hc : 0 < cut) (hs : supportOK p cut = true)
    (hk : ∀ mv : Move, mv.next.val ≤ cut → ∀ m,
      compatible (refine p s (some mv)) m → WeightedBound B m) :
    ∀ m, compatible p m → WeightedBound B m := by
  obtain ⟨c,hr,hrslot,hu,hb⟩ := firstHoleOK_sound h
  subst s
  exact tnf_branch_sound B cut p (readSlot c) hc (supportOK_sound hs) hu
    (knownRun_support p cut hc (supportOK_sound hs) n c hr) hf
    (first_hole_weighted_halt B p n c hf hr hu (delay_margin hb))
    (fun mv hv => hk mv (Nat.le_of_lt hv)) (fun q hq w r => hk ⟨w,r,q⟩ (Nat.le_of_eq hq))

theorem statesCases (q : Fin 6) : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega

def split (n : Nat) (s : Slot) (cut : Nat) (children : Array Tree) : Tree :=
  .split n s cut fun mv => children.getD (4*mv.next.val+2*mv.write.toNat+mv.right.toNat) .bad

#print axioms sound
#print axioms split_safe
end BB6.Agent5PhaseTree
