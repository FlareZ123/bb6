import WeightedTNFCertificate
import SideCycle
import TwoSidedAutomata
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Q0ExhaustiveTree
open BB6Coverage BB6.Agent13BlankDelay
open BB6Coverage.Agent50SideCycle
open BB6.Agent4Automata (Cert)
def slots : List Slot := (List.finRange 6).flatMap fun q => [(q,false),(q,true)]
theorem slots_mem (s : Slot) : s ∈ slots := by
  rcases s with ⟨q,b⟩
  apply List.mem_flatMap.mpr
  refine ⟨q,List.mem_finRange q,?_⟩
  cases b <;> simp
def moves : List Move := (List.finRange 6).flatMap fun q =>
  [⟨false,false,q⟩,⟨false,true,q⟩,⟨true,false,q⟩,⟨true,true,q⟩]
theorem moves_mem (m : Move) : m ∈ moves := by
  rcases m with ⟨w,r,q⟩
  apply List.mem_flatMap.mpr
  refine ⟨q,List.mem_finRange q,?_⟩
  cases w <;> cases r <;> simp
def idx (m : Move) := 4*m.next.val + 2*m.write.toNat + m.right.toNat
def sameTable (p q : PartialMachine) : Bool := slots.all fun s => decide (p s = q s)
theorem sameTable_sound {p q : PartialMachine} (h : sameTable p q = true) : p=q := by
  funext s
  exact of_decide_eq_true (List.all_eq_true.mp h s (slots_mem s))
theorem finite_known (p : PartialMachine) (n : Nat) (c : FinRayCfg)
    (h : finitePartialRun p n finiteBlank = some c) : knownRun p n = some (embedFinRay c) := by
  rw [weightedTNFKnownRun_eq_defaultRun]
  rw [← embedFinRay_blank]
  exact finitePartialRun_sound p _ (weightedTNFDefaultCompletion_compatible p) finiteBlank c n h
theorem delay_le5 (p : PartialMachine) (t : Fin 6) (d : Nat) (h : d ∈ possibleDelays p t) : d ≤ 5 := by
  have h' : d ∈ List.range 6 := (List.mem_filter.mp h).1
  exact Nat.lt_succ_iff.mp (List.mem_range.mp h')
def allOrdExcept (p : PartialMachine) (s : Slot) : Bool := slots.all fun t =>
  if t=s then true else match p t with | some (some _) => true | _ => false
theorem allOrdExcept_sound {p : PartialMachine} {s : Slot} (h : allOrdExcept p s = true) : ∀ t, t ≠ s → ∃ mv, p t = some (some mv) := by
  intro t ht
  have hh := List.all_eq_true.mp h t (slots_mem t)
  simp only [ite_eq_right ht] at hh
  cases he : p t with
  | none => simp [he] at hh
  | some tr => cases tr with
    | none => simp [he] at hh
    | some mv => exact ⟨mv,rfl⟩
def sideCheck (p : PartialMachine) (right : Bool) (entry period k : Nat) : Bool :=
  match finitePartialRun p entry finiteBlank with
  | none => false
  | some c => fastSideCycleCheck p entry period right (if right then c.head-(k:Int) else c.head+(k:Int)) && decide (period>0)
theorem sideCheck_sound (p : PartialMachine) (right : Bool) (entry period k : Nat)
    (h : sideCheck p right entry period k = true) : ∀ m, compatible p m → NeverHalts m := by
  unfold sideCheck at h
  split at h
  · contradiction
  · rename_i c hc
    simp only [Bool.and_eq_true] at h
    have hh := h
    exact fastSideCycleCheck_sound p entry period right _ (of_decide_eq_true hh.2) hh.1
inductive Tree where
  | fail
  | side (right : Bool) (entry period k : Nat)
  | pair (cert : Cert)
  | last (n : Nat)
  | symbolic
  | split (n : Nat) (kids : Array Tree)
def firstOK (p : PartialMachine) : Bool := decide (p initialSlot = some (some ⟨true,true,1⟩))
def holeOK (B : Nat) (p : PartialMachine) (n : Nat) (c : FinRayCfg) : Bool :=
  firstOK p && decide (p (readSlot (embedFinRay c)) = none) && decide (n+6 ≤ B)
def check (B : Nat) (sym : PartialMachine → Bool) : Nat → PartialMachine → Tree → Bool
  | 0, _, _ => false
  | fuel+1, p, t => match t with
    | .fail => false
    | .side right entry period k => sideCheck p right entry period k
    | .pair cert => BB6.Agent4Automata.check p cert
    | .symbolic => sym p
    | .last n => match finitePartialRun p n finiteBlank with
      | none => false
      | some c => holeOK B p n c && allOrdExcept p (readSlot (embedFinRay c))
    | .split n kids => match finitePartialRun p n finiteBlank with
      | none => false
      | some c => holeOK B p n c && moves.all fun mv =>
        check B sym fuel (refine p (readSlot (embedFinRay c)) (some mv)) (kids.getD (idx mv) .fail)
theorem holeOK_sound {B n : Nat} {p : PartialMachine} {c : FinRayCfg}
    (h : holeOK B p n c = true) :
    p initialSlot = some (some ⟨true,true,1⟩) ∧ p (readSlot (embedFinRay c)) = none ∧
      (∀ d ∈ possibleDelays (refine p (readSlot (embedFinRay c)) none) 0, d+n+1 ≤ B) := by
  simp only [holeOK, firstOK, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro d hd
  have hd' := delay_le5 _ _ _ hd
  omega
theorem check_sound (B : Nat) (sym : PartialMachine → Bool)
    (hsym : ∀ p, sym p = true → Cover (WeightedBound B) p)
    (fuel : Nat) (p : PartialMachine) (t : Tree) (h : check B sym fuel p t = true) :
    Cover (WeightedBound B) p := by
  induction fuel generalizing p t with
  | zero => contradiction
  | succ fuel ih =>
    cases t with
    | fail => contradiction
    | side right entry period k =>
      exact .leaf _ fun m hm => weighted_never B m (sideCheck_sound p right entry period k h m hm)
    | pair cert =>
      exact .leaf _ fun m hm => weighted_never B m (BB6.Agent4Automata.never p cert h m hm)
    | symbolic => exact hsym p h
    | last n =>
      simp only [check] at h
      split at h
      · contradiction
      · rename_i c hc
        simp only [Bool.and_eq_true] at h
        have hh := h
        obtain ⟨hf,hu,hd⟩ := holeOK_sound hh.1
        exact .leaf _ (last_hole_sound B p n (embedFinRay c) hf (finite_known p n c hc) hu
          (allOrdExcept_sound hh.2) hd)
    | split n kids =>
      simp only [check] at h
      split at h
      · contradiction
      · rename_i c hc
        simp only [Bool.and_eq_true] at h
        have hh := h
        obtain ⟨hf,hu,hd⟩ := holeOK_sound hh.1
        apply Cover.branch p (readSlot (embedFinRay c)) hu
        intro tr ht
        cases tr with
        | none => exact .leaf _ (first_hole_weighted_halt B p n (embedFinRay c) hf (finite_known p n c hc) hu hd)
        | some mv => exact ih _ _ (List.all_eq_true.mp hh.2 mv (moves_mem mv))
def splitOK (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) : Bool :=
  match finitePartialRun p n finiteBlank with
  | none => false
  | some c => holeOK B p n c && decide (readSlot (embedFinRay c) = s)
theorem split_sound (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot)
    (h : splitOK B p n s = true)
    (children : ∀ mv, Cover (WeightedBound B) (refine p s (some mv))) :
    Cover (WeightedBound B) p := by
  unfold splitOK at h
  split at h
  · contradiction
  · rename_i c hc
    simp only [Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨hf,hu,hd⟩ := holeOK_sound h.1
    have he := h.2
    subst s
    apply Cover.branch p (readSlot (embedFinRay c)) hu
    intro t ht
    cases t with
    | none => exact .leaf _ (first_hole_weighted_halt B p n (embedFinRay c) hf (finite_known p n c hc) hu hd)
    | some mv => exact children mv
#print axioms check_sound
#print axioms split_sound
end Q0ExhaustiveTree
