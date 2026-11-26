import Raw10Encoded
import WeightedFirstOneCover
import FiniteHalting
import ZipAuditCore
import TwoSidedAutomata

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent13.Box17
open BB6Coverage BB6.Agent13BlankDelay BB6Coverage.Agent10ZipAudit
open BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump
open BB6.Agent49Box

def slots : List Slot := (List.finRange 6).flatMap fun q => [(q,false),(q,true)]
theorem slots_complete (s : Slot) : s ∈ slots := by
  obtain ⟨q,b⟩ := s
  apply List.mem_flatMap.mpr
  refine ⟨q,List.mem_finRange q,?_⟩
  cases b <;> simp

def index (s : Slot) : Fin 12 := ⟨2*s.1.val+s.2.toNat, by have := s.1.isLt; have := Bool.toNat_lt s.2; omega⟩
def slot (i : Fin 12) : Slot := (⟨i.val/2,by have := i.isLt; omega⟩,i.val%2==1)
theorem index_slot (i : Fin 12) : index (slot i) = i := by revert i; decide
theorem slot_index (s : Slot) : slot (index s) = s := by
  rcases s with ⟨q,b⟩
  revert q b
  decide

def decode (v : Fin 25) : Transition :=
  if v.val=0 then none else let j:=v.val-1; some ⟨(j/2)%2==1,j%2==1,⟨j/4,by have := v.isLt; omega⟩⟩
def literalDomain (i : Fin 12) : List (Fin 25) :=
  match i.val with
  | 0 => [8]
  | 1 => [0,1,4,5,7,9,10,11,12,13,14,15,16,20,21,22,23,24]
  | 2 => [11]
  | 3 => [6]
  | 4 => [17]
  | 5 => [13]
  | 6 => [11]
  | 7 => List.finRange 25
  | 8 => [2]
  | 9 => [23]
  | 10 => [0,2,3,4,11,12,14,15,16,19,20,22,24]
  | _ => List.finRange 25

def domain : Box Slot Transition := fun s => (literalDomain (index s)).map decode

theorem literalDomain_matches : ∀ i : Fin 12, literalDomain i = BB6.Agent49BoxEncoded.boxes[17]! i := by decide

def root : PartialMachine := fun s =>
  match literalDomain (index s) with
  | [v] => some (decode v)
  | _ => none

theorem root_compatible (m : Machine) (h : Fits domain m) : compatible root m := by
  intro s t ht
  unfold root at ht
  cases he : literalDomain (index s) with
  | nil => simp [he] at ht
  | cons a as =>
    cases as with
    | nil =>
      have hmem := h s
      simp [domain,he] at hmem
      simp [he] at ht
      exact hmem.trans ht
    | cons b bs => simp [he] at ht

def ordinaryExcept (p : PartialMachine) (s : Slot) : Bool :=
  slots.all fun t => if t=s then true else match p t with | some (some _) => true | _ => false

theorem ordinaryExcept_sound (p : PartialMachine) (s : Slot)
    (h : ordinaryExcept p s = true) (m : Machine) (hm : compatible p m)
    (hs : ∃ mv, m s = some mv) : NeverHalts m := by
  apply all_ordinary_never
  intro t
  by_cases hts : t=s
  · simpa [hts] using hs
  · have hv := List.all_eq_true.mp h t (slots_complete t)
    simp only [hts,ite_false] at hv
    cases hpt : p t with
    | none => simp [hpt] at hv
    | some a =>
      cases a with
      | none => simp [hpt] at hv
      | some mv => exact ⟨mv,hm t _ hpt⟩

def tableEq (a b : PartialMachine) : Bool := slots.all fun s => decide (a s=b s)
theorem tableEq_sound (a b : PartialMachine) (h : tableEq a b = true) : a=b := by
  funext s
  exact of_decide_eq_true (List.all_eq_true.mp h s (slots_complete s))

def firstOne (p : PartialMachine) : Bool := decide (p initialSlot=some (some ⟨true,true,1⟩))
def zipHalt (p : PartialMachine) (n : Nat) : Bool :=
  match zipRead p n with | some s => decide (p s = some none) | none => false

theorem zipHalt_sound (p : PartialMachine) (n : Nat) (h : zipHalt p n = true)
    (m : Machine) (hm : compatible p m) : HaltsAfter m n := by
  unfold zipHalt zipRead at h
  cases he : zrun p n start with
  | none => simp [he] at h
  | some z =>
    have hp : p (z.q,z.l.headD false)=some none := by simpa [he] using h
    have hs := zrun_sound p m hm n start z he
    rw [start_embed] at hs
    have ht := hm _ _ hp
    constructor
    · change (run m n blank).isSome = true
      rw [hs]; rfl
    · change (run m n blank).bind (rawStep m) = none
      rw [hs]
      simp only [Option.bind_some,rawStep,read_embed,ht,Option.map_none]

def haltBound (p : PartialMachine) (n B : Nat) : Bool :=
  zipHalt p n && firstOne p && (possibleDelays p 0).all (fun d => decide (d+n+1≤B))

theorem haltBound_sound (p : PartialMachine) (n B : Nat) (h : haltBound p n B = true)
    (m : Machine) (hm : compatible p m) : WeightedBound B m := by
  simp only [haltBound, Bool.and_eq_true] at h
  have hhalt := zipHalt_sound p n h.1.1 m hm
  intro k d hk hd
  have he := halting_time_unique m k n hk hhalt
  have hfirst : p initialSlot=some (some ⟨true,true,1⟩) := of_decide_eq_true h.1.2
  have hmem := delays_subset_possible p m hm 0 (firstOne_terminal p hfirst m hm) d hd
  have hb := of_decide_eq_true (List.all_eq_true.mp h.2 d hmem)
  omega

inductive Witness where
  | halt (n : Nat)
  | cycle (entry period : Nat) (right : Bool) (boundary : Int)
  | last (s : Fin 12) (n : Nat)
  | cert (i : Nat)
  deriving Inhabited

inductive Tree where
  | leaf (w : Witness)
  | branch (s : Fin 12) (kids : List (Fin 25 × Tree))
  deriving Inhabited

-- Every external certificate is tied to its actual table, never to an unchecked integer ID.
def leafCheck (B : Nat) (known : Array PartialMachine) (p : PartialMachine) : Witness → Bool
  | .halt n => haltBound p n B
  | .cycle entry period right boundary => decide (0<period) && zipCycle p entry period right boundary
  | .last i n => ordinaryExcept p (slot i) && haltBound (refine p (slot i) none) n B
  | .cert i => match known[i]? with | some q => tableEq p q | none => false

theorem leafCheck_sound (B : Nat) (known : Array PartialMachine)
    (hknown : ∀ (i : Nat) (q : PartialMachine), known[i]? = some q → ∀ m, compatible q m → WeightedBound B m)
    (p : PartialMachine) (w : Witness) (h : leafCheck B known p w = true)
    (m : Machine) (hm : compatible p m) : WeightedBound B m := by
  cases w with
  | halt n => exact haltBound_sound p n B h m hm
  | cycle entry period right boundary =>
    simp only [leafCheck,Bool.and_eq_true] at h
    exact weighted_of_never B m (zipCycle_sound p entry period right boundary (of_decide_eq_true h.1) h.2 m hm)
  | last i n =>
    simp only [leafCheck,Bool.and_eq_true] at h
    cases he : m (slot i) with
    | none =>
      apply haltBound_sound _ n B h.2 m
      simpa [he] using compatible_refine p m (slot i) hm
    | some mv => exact weighted_of_never B m (ordinaryExcept_sound p (slot i) h.1 m hm ⟨mv,he⟩)
  | cert i =>
    cases he : known[i]? with
    | none => simp [leafCheck,he] at h
    | some q =>
      have heq : p=q := tableEq_sound p q (by simpa [leafCheck,he] using h)
      exact hknown i q he m (heq ▸ hm)

def audit (B : Nat) (known : Array PartialMachine) : Nat → PartialMachine → Tree → Bool
  | _,p,.leaf w => leafCheck B known p w
  | 0,_,.branch _ _ => false
  | fuel+1,p,.branch s kids =>
    (kids.map Prod.fst == literalDomain s) &&
    kids.all (fun (v,t) => audit B known fuel (refine p (slot s) (decode v)) t)

theorem audit_sound (B : Nat) (known : Array PartialMachine)
    (hknown : ∀ (i : Nat) (q : PartialMachine), known[i]? = some q → ∀ m, compatible q m → WeightedBound B m)
    (fuel : Nat) (p : PartialMachine) (t : Tree) (h : audit B known fuel p t = true)
    (m : Machine) (hdom : Fits domain m) (hm : compatible p m) : WeightedBound B m := by
  induction fuel generalizing p t with
  | zero =>
    cases t with
    | leaf w => exact leafCheck_sound B known hknown p w h m hm
    | branch s kids => simp [audit] at h
  | succ fuel ih =>
    cases t with
    | leaf w => exact leafCheck_sound B known hknown p w h m hm
    | branch s kids =>
      simp only [audit,Bool.and_eq_true,beq_iff_eq] at h
      have hmem := hdom (slot s)
      simp only [domain,index_slot,List.mem_map] at hmem
      obtain ⟨v,hv,he⟩ := hmem
      rw [←h.1] at hv
      obtain ⟨⟨w,u⟩,hmem,hw⟩ := List.mem_map.mp hv
      dsimp at hw
      subst w
      apply ih (refine p (slot s) (decode v)) u (List.all_eq_true.mp h.2 (v,u) hmem)
      rw [he]
      exact compatible_refine p m (slot s) hm

#print axioms audit_sound
#print axioms literalDomain_matches
end BB6.Agent13.Box17
