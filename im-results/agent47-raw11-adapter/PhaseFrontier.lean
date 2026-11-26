import PhaseTree

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47PhaseFrontier
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent1NGram BB6.Agent5PhaseTree

/-- A mixed proof / frontier tree. A supplied proof is accepted only after
    exact table equality is checked; unresolved leaves remain explicit. -/
inductive Route (B : Nat) where
  | pending
  | closed (t : Tree)
  | certified (q : PartialMachine) (safe : ∀ m, compatible q m → WeightedBound B m)
  | split (n : Nat) (s : Slot) (cut : Nat) (kids : Move → Route B)

def choices (cut : Nat) : List Move :=
  (List.finRange 6).flatMap fun q =>
    if q.val ≤ cut then [⟨false,false,q⟩,⟨false,true,q⟩,⟨true,false,q⟩,⟨true,true,q⟩] else []

theorem choice_mem (cut : Nat) (mv : Move) (h : mv.next.val ≤ cut) : mv ∈ choices cut := by
  apply List.mem_flatMap.mpr
  refine ⟨mv.next,List.mem_finRange _,?_⟩
  rcases mv with ⟨w,r,q⟩
  cases w <;> cases r <;> simp [h]

def sameTable (p q : PartialMachine) : Bool :=
  (List.finRange 6).all fun s => bits.all fun b => decide (p (s,b) = q (s,b))

theorem sameTable_sound {p q : PartialMachine} (h : sameTable p q = true) : p = q := by
  funext s
  rcases s with ⟨r,b⟩
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h r (mem_states r)) b (mem_bits b))

def check (B : Nat) (p : PartialMachine) : Route B → Bool
  | .pending => true
  | .closed t => BB6.Agent5PhaseTree.check B p t
  | .certified q _ => sameTable p q
  | .split n s cut kids => firstHoleOK B p n s && decide (0 < cut) && supportOK p cut &&
      (choices cut).all fun mv => check B (refine p s (some mv)) (kids mv)

def residuals (B : Nat) (p : PartialMachine) : Route B → List PartialMachine
  | .pending => [p]
  | .closed _ | .certified _ _ => []
  | .split _ s cut kids => (choices cut).flatMap fun mv =>
      residuals B (refine p s (some mv)) (kids mv)

theorem consume (B : Nat) (p : PartialMachine) (t : Route B)
    (hf : p initialSlot = some (some ⟨true,true,1⟩)) (hc : check B p t = true)
    (hr : ∀ q ∈ residuals B p t, ∀ m, compatible q m → WeightedBound B m) :
    ∀ m, compatible p m → WeightedBound B m := by
  induction t generalizing p with
  | pending => exact hr p (by simp [residuals])
  | closed t => exact BB6.Agent5PhaseTree.sound B p t hf hc
  | certified q safe =>
    have he : p = q := sameTable_sound hc
    subst q
    exact safe
  | split n s cut kids ih =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
    apply split_safe B p n s cut hf hc.1.1.1 hc.1.1.2 hc.1.2
    intro mv hmv
    have hm := choice_mem cut mv hmv
    obtain ⟨c,_,_,hu,_⟩ := firstHoleOK_sound hc.1.1.1
    apply ih mv _ (refine_preserves_firstOne p s (some mv) hu hf) (List.all_eq_true.mp hc.2 mv hm)
    intro q hq
    exact hr q (List.mem_flatMap.mpr ⟨mv,hm,hq⟩)

def split {B : Nat} (n : Nat) (s : Slot) (cut : Nat) (kids : Array (Route B)) : Route B :=
  .split n s cut fun mv => kids.getD (4*mv.next.val+2*mv.write.toNat+mv.right.toNat) .pending

/-- A halt and an unassigned row have distinct codes. -/
def slotCode : Option (Option Move) → Nat
  | none => 24
  | some none => 25
  | some (some mv) => 4*mv.next.val+2*mv.write.toNat+mv.right.toNat

def tableCode (p : PartialMachine) : Nat :=
  ((List.finRange 6).flatMap fun q => [slotCode (p (q,false)),slotCode (p (q,true))]).foldl (fun a b => 26*a+b) 0

theorem liftBound {A B : Nat} (hAB : A ≤ B) {m : Machine} (h : WeightedBound A m) : WeightedBound B m := by
  intro k d hk hd
  exact Nat.le_trans (h k d hk hd) hAB

/-- The certified local cap can be lifted to the global candidate bound,
    while the remaining cylinders are allowed any larger common cap. -/
theorem consumeAt (A B : Nat) (hAB : A ≤ B) (p : PartialMachine) (t : Route A)
    (hf : p initialSlot = some (some ⟨true,true,1⟩)) (hc : check A p t = true)
    (hr : ∀ q ∈ residuals A p t, ∀ m, compatible q m → WeightedBound B m) :
    ∀ m, compatible p m → WeightedBound B m := by
  induction t generalizing p with
  | pending => exact hr p (by simp [residuals])
  | closed t => exact fun m hm => liftBound hAB (BB6.Agent5PhaseTree.sound A p t hf hc m hm)
  | certified q safe =>
    have he : p = q := sameTable_sound hc
    subst q
    exact fun m hm => liftBound hAB (safe m hm)
  | split n s cut kids ih =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
    have hbig : firstHoleOK B p n s = true := by
      simp only [firstHoleOK,Bool.and_eq_true,decide_eq_true_eq] at hc ⊢
      exact ⟨hc.1.1.1.1, Nat.le_trans hc.1.1.1.2 hAB⟩
    apply split_safe B p n s cut hf hbig hc.1.1.2 hc.1.2
    intro mv hmv
    have hm := choice_mem cut mv hmv
    obtain ⟨c,_,_,hu,_⟩ := firstHoleOK_sound hc.1.1.1
    apply ih mv _ (refine_preserves_firstOne p s (some mv) hu hf) (List.all_eq_true.mp hc.2 mv hm)
    intro q hq
    exact hr q (List.mem_flatMap.mpr ⟨mv,hm,hq⟩)

#print axioms consumeAt

#print axioms consume
#print axioms sameTable_sound
end BB6.Agent47PhaseFrontier
