import Box17AuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent13.Box16
open BB6Coverage BB6.Agent13BlankDelay BB6Coverage.Agent10ZipAudit
open BB6.Agent49Box BB6.Agent13.Box17
def literalDomain (i : Fin 12) : List (Fin 25) :=
  match i.val with
  | 0 => [8]
  | 1 => List.finRange 25
  | 2 => [11]
  | 3 => [6]
  | 4 => [17]
  | 5 => [13]
  | 6 => [11]
  | 7 => List.finRange 25
  | 8 => [2]
  | 9 => [0,7,15,18,19,20,21,22,24]
  | 10 => List.finRange 25
  | _ => List.finRange 25

def domain : Box Slot Transition := fun s => (literalDomain (index s)).map decode

theorem literalDomain_matches : ∀ i : Fin 12, literalDomain i = BB6.Agent49BoxEncoded.boxes[16]! i := by decide

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

def Good (p : PartialMachine) : Prop := ∀ m, BB6.Agent49Box.Fits domain m → compatible p m → WeightedBound 7376 m

theorem good_of_bound (p : PartialMachine) (h : ∀ m, compatible p m → WeightedBound 7376 m) : Good p :=
  fun m _ hm => h m hm

theorem good_never (p : PartialMachine) (h : ∀ m, compatible p m → NeverHalts m) : Good p :=
  good_of_bound p (fun m hm => weighted_of_never 7376 m (h m hm))

theorem good_halt (p : PartialMachine) (n : Nat) (h : haltBound p n 7376 = true) : Good p :=
  good_of_bound p (haltBound_sound p n 7376 h)

theorem good_cycle (p : PartialMachine) (entry period : Nat) (right : Bool) (boundary : Int)
    (hp : 0 < period) (h : zipCycle p entry period right boundary = true) : Good p :=
  good_never p (zipCycle_sound p entry period right boundary hp h)

theorem good_last (p : PartialMachine) (s : Slot) (n : Nat)
    (he : ordinaryExcept p s = true) (hh : haltBound (refine p s none) n 7376 = true) : Good p := by
  apply good_of_bound
  intro m hm
  cases h : m s with
  | none =>
    apply haltBound_sound _ n 7376 hh m
    simpa [h] using compatible_refine p m s hm
  | some mv => exact weighted_of_never 7376 m (ordinaryExcept_sound p s he m hm ⟨mv,h⟩)

theorem good_split (p : PartialMachine) (s : Fin 12)
    (h : ∀ v ∈ literalDomain s, Good (refine p (slot s) (decode v))) : Good p := by
  intro m hdom hm
  have hmem := hdom (slot s)
  simp only [domain,index_slot,List.mem_map] at hmem
  obtain ⟨v,hv,he⟩ := hmem
  apply h v hv m hdom
  rw [he]
  exact compatible_refine p m (slot s) hm


#print axioms good_split
end BB6.Agent13.Box16
