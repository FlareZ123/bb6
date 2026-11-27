import Box33Residual
import WeightedBoxOneHalt
import DomainPackedStack

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent13.Box33Direct
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box
open BB6.Agent13.Box17 BB6.Agent13BoxOneHalt BB6Coverage.Agent10ZipAudit

def Good (B : Nat) (p : PartialMachine) : Prop :=
  ∀ m, compatible p m → WeightedBound B m

theorem good_halt (B : Nat) (p : PartialMachine) (n : Nat)
    (h : haltBound p n B = true) : Good B p :=
  fun m hm => haltBound_sound p n B h m hm

theorem good_short (B : Nat) (p : PartialMachine) (n : Nat)
    (h : zipHalt p n = true) (hb : n + 6 ≤ B) : Good B p := by
  intro m hm
  have hhalt := zipHalt_sound p n h m hm
  intro k d hk hd
  have he := halting_time_unique m k n hk hhalt
  have hh := List.mem_range.mp (List.mem_filter.mp hd).1
  omega

theorem good_never (B : Nat) (p : PartialMachine)
    (h : ∀ m, compatible p m → NeverHalts m) : Good B p :=
  fun m hm => weighted_of_never _ _ (h m hm)

theorem good_split (B : Nat) (p : PartialMachine) (i : Fin 12)
    (h : ∀ v : Fin 25, Good B (refine p (slot i) (decode v))) : Good B p := by
  intro m hm
  obtain ⟨v,hv⟩ := Box33D0.decode_complete (m (slot i))
  apply h v m
  rw [hv]
  exact compatible_refine p m (slot i) hm

/-- For a table with eleven ordinary transitions, only the missing row's
halt completion requires checking; every other completion is total. -/
theorem good_last (B : Nat) (p : PartialMachine) (i : Fin 12)
    (ho : ordinaryExcept p (slot i) = true)
    (hh : Good B (refine p (slot i) none)) : Good B p := by
  intro m hm
  cases he : m (slot i) with
  | none =>
    apply hh m
    simpa [he] using compatible_refine p m (slot i) hm
  | some mv =>
    exact weighted_of_never _ _ (ordinaryExcept_sound p (slot i) ho m hm ⟨mv,he⟩)

def restrict (p : PartialMachine) : Box Slot Transition :=
  fun s => match p s with
  | none => choices
  | some t => [t]

theorem fits_restrict (p : PartialMachine) (m : Machine)
    (hm : compatible p m) : Fits (restrict p) m := by
  intro s
  unfold restrict
  cases h : p s with
  | none => exact choices_complete _
  | some t => simp [hm s t h]

structure Known (B : Nat) where
  p : PartialMachine
  good : Good B p

structure SafeBox where
  box : Box Slot Transition
  safe : ∀ m, Fits box m → NeverHalts m

def subsetCheck (p : PartialMachine) (b : Box Slot Transition) : Bool :=
  slots.all (fun s => (restrict p s).all (fun v => (b s).contains v))

theorem subsetCheck_sound (B : Nat) (p : PartialMachine) (b : SafeBox)
    (h : subsetCheck p b.box = true) : Good B p := by
  apply good_never B p
  intro m hm
  apply b.safe m
  intro s
  have hs := List.all_eq_true.mp h s (slots_complete s)
  exact List.contains_iff_mem.mp (List.all_eq_true.mp hs (m s) (fits_restrict p m hm s))

structure Bank (B : Nat) where
  known : Array (Known B)
  boxes : Array SafeBox

inductive Witness where
  | short (n : Nat)
  | exact (n : Nat)
  | cycle (entry period : Nat) (right : Bool) (boundary : Int)
  | known (i : Nat)
  | box (i : Nat)
  deriving Inhabited

inductive Tree where
  | leaf (w : Witness)
  | branch (s : Fin 12) (kids : List (Fin 25 × Tree))
  | last (s : Fin 12) (kid : Tree)
  deriving Inhabited

def checkLeaf {B : Nat} (bank : Bank B)
    (p : PartialMachine) : Witness → Bool
  | .short n => zipHalt p n && decide (n+6 ≤ B)
  | .exact n => haltBound p n B
  | .cycle e k r b => decide (0<k) && zipCycle p e k r b
  | .known i => match bank.known[i]? with | some v => tableEq p v.p | none => false
  | .box i => match bank.boxes[i]? with | some b => subsetCheck p b.box | none => false

theorem checkLeaf_sound {B : Nat} (bank : Bank B)
    (p : PartialMachine) (w : Witness) (h : checkLeaf bank p w = true) :
    Good B p := by
  cases w with
  | short n =>
    simp only [checkLeaf,Bool.and_eq_true] at h
    exact good_short B p n h.1 (of_decide_eq_true h.2)
  | exact n => exact good_halt B p n h
  | cycle e k r b =>
    simp only [checkLeaf,Bool.and_eq_true] at h
    exact good_never B p (zipCycle_sound p e k r b (of_decide_eq_true h.1) h.2)
  | box i =>
    cases he : bank.boxes[i]? with
    | none => simp [checkLeaf,he] at h
    | some b => exact subsetCheck_sound B p b (by simpa [checkLeaf,he] using h)
  | known i =>
    cases he : bank.known[i]? with
    | none => simp [checkLeaf,he] at h
    | some q =>
      have hp := tableEq_sound p q.p (by simpa [checkLeaf,he] using h)
      exact hp.symm ▸ q.good

def audit {B : Nat} (bank : Bank B) : Nat → PartialMachine → Tree → Bool
  | _,p,.leaf w => checkLeaf bank p w
  | 0,_,_ => false
  | fuel+1,p,.branch s kids =>
    (kids.map Prod.fst == List.finRange 25) &&
      kids.all (fun (v,t) => audit bank fuel (refine p (slot s) (decode v)) t)
  | fuel+1,p,.last s kid =>
    ordinaryExcept p (slot s) && audit bank fuel (refine p (slot s) none) kid

theorem audit_sound {B : Nat} (bank : Bank B)
    (fuel : Nat) (p : PartialMachine) (t : Tree)
    (h : audit bank fuel p t = true) : Good B p := by
  induction fuel generalizing p t with
  | zero =>
    cases t with
    | leaf w => exact checkLeaf_sound bank p w h
    | branch s kids => simp [audit] at h
    | last s kid => simp [audit] at h
  | succ fuel ih =>
    cases t with
    | leaf w => exact checkLeaf_sound bank p w h
    | branch s kids =>
      simp only [audit,Bool.and_eq_true,beq_iff_eq] at h
      apply good_split B p s
      intro v
      have hv : v ∈ List.finRange 25 := List.mem_finRange v
      rw [← h.1] at hv
      obtain ⟨⟨w,u⟩,hmem,hw⟩ := List.mem_map.mp hv
      dsimp at hw
      subst w
      exact ih _ u (List.all_eq_true.mp h.2 (v,u) hmem)
    | last s kid =>
      simp only [audit,Bool.and_eq_true] at h
      exact good_last B p s h.1 (ih _ _ h.2)

def certified {B : Nat} (bank : Bank B) (p : PartialMachine)
    (t : Tree) (h : audit bank 12 p t = true) : Known B :=
  ⟨p,audit_sound bank 12 p t h⟩

#print axioms good_last
#print axioms audit_sound
end BB6.Agent13.Box33Direct
