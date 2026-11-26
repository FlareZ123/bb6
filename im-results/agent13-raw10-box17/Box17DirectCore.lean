import Box17Lower
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent13.Box17
open BB6Coverage BB6.Agent13BlankDelay BB6Coverage.Agent10ZipAudit

def r1Table : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨false,false,2⟩)
  | (1,false) => some (some ⟨true,false,2⟩)
  | (1,true) => some (some ⟨false,true,1⟩)
  | (2,false) => some (some ⟨false,false,4⟩)
  | (2,true) => some (some ⟨false,false,3⟩)
  | (3,false) => some (some ⟨true,false,2⟩)
  | (3,true) => none
  | (4,false) => some (some ⟨false,true,0⟩)
  | (4,true) => some (some ⟨true,false,5⟩)
  | (5,false) => some (some ⟨true,false,0⟩)
  | (5,true) => some (some ⟨true,false,5⟩)
  | _ => none

def r1Machine : Machine := fun s => (r1Table s).getD none

def Good (p : PartialMachine) : Prop := NeverHalts r1Machine → ∀ m, BB6.Agent49Box.Fits domain m → compatible p m → WeightedBound 7014 m

theorem good_of_bound (p : PartialMachine) (h : ∀ m, compatible p m → WeightedBound 7014 m) : Good p :=
  fun _ m _ hm => h m hm

theorem good_never (p : PartialMachine) (h : ∀ m, compatible p m → NeverHalts m) : Good p :=
  good_of_bound p (fun m hm => weighted_of_never 7014 m (h m hm))

theorem good_halt (p : PartialMachine) (n : Nat) (h : haltBound p n 7014 = true) : Good p :=
  good_of_bound p (haltBound_sound p n 7014 h)

theorem good_cycle (p : PartialMachine) (entry period : Nat) (right : Bool) (boundary : Int)
    (hp : 0 < period) (h : zipCycle p entry period right boundary = true) : Good p :=
  good_never p (zipCycle_sound p entry period right boundary hp h)

theorem good_last (p : PartialMachine) (s : Slot) (n : Nat)
    (he : ordinaryExcept p s = true) (hh : haltBound (refine p s none) n 7014 = true) : Good p := by
  apply good_of_bound
  intro m hm
  cases h : m s with
  | none =>
    apply haltBound_sound _ n 7014 hh m
    simpa [h] using compatible_refine p m s hm
  | some mv => exact weighted_of_never 7014 m (ordinaryExcept_sound p s he m hm ⟨mv,h⟩)

theorem good_split (p : PartialMachine) (s : Fin 12)
    (h : ∀ v ∈ literalDomain s, Good (refine p (slot s) (decode v))) : Good p := by
  intro hr1 m hdom hm
  have hmem := hdom (slot s)
  simp only [domain,index_slot,List.mem_map] at hmem
  obtain ⟨v,hv,he⟩ := hmem
  apply h v hv hr1 m hdom
  rw [he]
  exact compatible_refine p m (slot s) hm

theorem good_r1 : Good r1Table := by
  intro hr1 m _ hm
  cases hd : m (slot 7) with
  | some mv => exact weighted_of_never _ _ (ordinaryExcept_sound _ _ (by decide) _ hm ⟨mv,hd⟩)
  | none =>
    have he : m = r1Machine := by
      funext s
      by_cases hs : s = slot 7
      · rw [hs]; exact hd
      · have hknown : ∀ t : Slot, t ≠ slot 7 → (r1Table t).isSome = true := by
          intro t
          obtain ⟨q,b⟩ := t
          revert q b
          decide
        have hv := hknown s hs
        cases ht : r1Table s with
        | none => simp [ht] at hv
        | some t => simpa [r1Machine,ht] using hm s t ht
    exact weighted_of_never _ _ (he.symm ▸ hr1)

#print axioms good_split
#print axioms good_r1
end BB6.Agent13.Box17
