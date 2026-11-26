import Box17AuditCore
import WeightedBoxOneHalt
import WeightedBoxMinimalHalt
import Raw10EncodedSourceBridge
import DomainPackedStack

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent13.Box4
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box
open BB6.Agent13.Box17 BB6.Agent49BoxBridge BB6.Agent13BoxOneHalt
open BB6Coverage.Agent10ZipAudit BB6.Agent13BitPacked BB6.Agent13DomainPacked

def literalDomain (i : Fin 12) : List (Fin 25) :=
  match i.val with
  | 0 => [8]
  | 1 => [14]
  | 2 => [11]
  | 3 => [7]
  | 4 => [17]
  | 5 => [4]
  | 6 => (List.finRange 25).filter (· != 9)
  | _ => List.finRange 25

def domain : Box Slot Transition := fun s => (literalDomain (index s)).map decode
theorem literalDomain_matches : ∀ i : Fin 12, literalDomain i = BB6.Agent49BoxEncoded.boxes[4]! i := by decide

theorem index_source (s : Slot) : index s = BB6.Agent17Raw10BoxFar.slotIndex s := by
  rcases s with ⟨q,b⟩
  revert q b
  decide

theorem decode_source (v : Fin 25) : decode v = BB6.Agent17Raw10BoxFar.decodeCode v := by
  revert v
  decide

theorem sourceDomainEq : domain = raw10Remainder[4]! := by
  funext s
  have h := BB6.Agent17Raw10BoxFar.exact_box_at_index (4 : Fin 34) s
  change raw10Remainder[4]! s =
    (BB6.Agent49BoxEncoded.boxes[4]! (BB6.Agent17Raw10BoxFar.slotIndex s)).map BB6.Agent17Raw10BoxFar.decodeCode at h
  unfold domain
  rw [h, literalDomain_matches, index_source]
  rw [show decode = BB6.Agent17Raw10BoxFar.decodeCode from funext decode_source]

def sliceDomain (target i : Fin 12) : List (Fin 25) :=
  (literalDomain i).filter (fun v => (v == 0) == (i == target))

def sliceBox (target : Fin 12) : Box Slot Transition :=
  fun s => (sliceDomain target (index s)).map decode

theorem slice_eq : ∀ (t : Fin 12) (q : Fin 6) (b : Bool),
    sliceBox t (q,b) = haltSlice domain (slot t) (q,b) := by decide

theorem slice_eq_fun (t : Fin 12) : sliceBox t = haltSlice domain (slot t) := by
  funext s
  obtain ⟨q,b⟩ := s
  exact slice_eq t q b

def fallback : Slot → Move := fun _ => ⟨true,false,0⟩
theorem fallback_valid (s : Slot) : none ∈ domain s → some (fallback s) ∈ domain s := by
  rcases s with ⟨q,b⟩
  revert q b
  decide

theorem slices_iff (B : Nat) :
    (∀ m, Fits domain m → WeightedBound B m) ↔
      ∀ t : Fin 12, ∀ m, Fits (sliceBox t) m → WeightedBound B m := by
  rw [oneHaltSlices_iff _ fallback fallback_valid (fun _ => rfl) B]
  constructor
  · intro h t m hm
    exact h (slot t) m (slice_eq_fun t ▸ hm)
  · intro h s m hm
    have he := slice_eq_fun (index s)
    rw [slot_index] at he
    exact h (index s) m (he.symm ▸ hm)

def root (target : Fin 12) : PartialMachine := fun s =>
  match sliceDomain target (index s) with
  | [v] => some (decode v)
  | _ => none

theorem root_compatible (target : Fin 12) (m : Machine) (h : Fits (sliceBox target) m) :
    compatible (root target) m := by
  intro s t ht
  unfold root at ht
  cases he : sliceDomain target (index s) with
  | nil => simp [he] at ht
  | cons a as =>
    cases as with
    | nil =>
      have hmem := h s
      simp [sliceBox,he] at hmem
      simp [he] at ht
      exact hmem.trans ht
    | cons b bs => simp [he] at ht

def Good (target : Fin 12) (p : PartialMachine) : Prop :=
  ∀ m, Fits (sliceBox target) m → compatible p m → WeightedBound 3640 m

theorem good_halt (target : Fin 12) (p : PartialMachine) (n : Nat)
    (h : haltBound p n 3640 = true) : Good target p :=
  fun m _ hm => haltBound_sound p n 3640 h m hm

theorem short_halt_bound (p : PartialMachine) (n : Nat)
    (h : zipHalt p n = true) (hb : n + 6 ≤ 3640)
    (m : Machine) (hm : compatible p m) : WeightedBound 3640 m := by
  have hhalt := zipHalt_sound p n h m hm
  intro k d hk hd
  have he := halting_time_unique m k n hk hhalt
  have hh := List.mem_range.mp (List.mem_filter.mp hd).1
  omega

theorem good_short (target : Fin 12) (p : PartialMachine) (n : Nat)
    (h : zipHalt p n = true) (hb : n + 6 ≤ 3640) : Good target p :=
  fun m _ hm => short_halt_bound p n h hb m hm

theorem good_never (target : Fin 12) (p : PartialMachine)
    (h : ∀ m, compatible p m → NeverHalts m) : Good target p :=
  fun m _ hm => weighted_of_never _ _ (h m hm)

theorem good_cycle (target : Fin 12) (p : PartialMachine) (entry period : Nat)
    (right : Bool) (boundary : Int) (hp : 0 < period)
    (h : zipCycle p entry period right boundary = true) : Good target p :=
  good_never target p (zipCycle_sound p entry period right boundary hp h)

theorem good_split (target : Fin 12) (p : PartialMachine) (s : Fin 12)
    (h : ∀ v ∈ sliceDomain target s, Good target (refine p (slot s) (decode v))) :
    Good target p := by
  intro m hdom hm
  have hmem := hdom (slot s)
  simp only [sliceBox,index_slot,List.mem_map] at hmem
  obtain ⟨v,hv,he⟩ := hmem
  apply h v hv m hdom
  rw [he]
  exact compatible_refine p m (slot s) hm

def restrict (target : Fin 12) (p : PartialMachine) : Box Slot Transition :=
  fun s => match p s with
  | none => sliceBox target s
  | some t => [t]

theorem fits_restrict (target : Fin 12) (p : PartialMachine) (m : Machine)
    (hd : Fits (sliceBox target) m) (hm : compatible p m) : Fits (restrict target p) m := by
  intro s
  cases h : p s with
  | none => simpa [restrict,h] using hd s
  | some t => simp [restrict,h,hm s t h]

theorem good_cert (target : Fin 12) (p : PartialMachine) (c : Cert)
    (h : checkDomain (restrict target p) c = true) : Good target p := by
  intro m hd hm
  exact weighted_of_never _ _ (neverDomain _ c h m (fits_restrict target p m hd hm))

/-- Any larger certified box may cover a smaller first-hole cylinder. -/
theorem good_superbox (target : Fin 12) (p : PartialMachine) (b : Box Slot Transition)
    (h : ∀ s v, v ∈ restrict target p s → v ∈ b s)
    (safe : ∀ m, Fits b m → NeverHalts m) : Good target p := by
  intro m hd hm
  exact weighted_of_never _ _ (safe m (fun s => h s (m s) (fits_restrict target p m hd hm s)))

/-- All six fixed slots are ordinary; the other six are the only possible
    designated final halt slots. -/
theorem source_upper (h : ∀ t : Fin 12, 6 ≤ t.val → Good t (root t)) :
    ∀ m, Fits raw10Remainder[4]! m → WeightedBound 3640 m := by
  rw [← sourceDomainEq, slices_iff]
  intro t m hm
  by_cases ht : 6 ≤ t.val
  · exact h t ht m hm (root_compatible t m hm)
  · have he : ∀ i : Fin 12, i.val < 6 → sliceDomain i i = [] := by decide
    have hz := hm (slot t)
    simp only [sliceBox,index_slot,he t (by omega),List.map_nil,List.not_mem_nil] at hz

#print axioms source_upper
#print axioms good_superbox
end BB6.Agent13.Box4
