import Box27D0FastPumps
import Box27D17Parent
import Box27Symmetry

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent49.Box27CanonicalFrontier
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode slot)
open BB6.Agent49.Box27Symmetry (ef efCode ef_code_decode fits_renamed decode_surjective)
open BB6.Agent16WeightedSymmetry

def sourceD0 : List (Fin 25) :=
  [0,2,3,4,5,6,7,9,10,12,14,16,17,18,19,20,21,22,23,24]

theorem sourceD0eq : raw10Remainder[27]! (3,false) = sourceD0.map decode := by decide

def query (d : Fin 25) : Fin 12 :=
  if d.val ≤ 4 then 3 else if d.val ≤ 16 then 7 else if d.val ≤ 20 then 8 else 10

def child (d v : Fin 25) (m : Machine) : Prop :=
  Fits raw10Remainder[27]! m ∧ m (3,false) = decode d ∧ m (slot (query d)) = decode v

def early (d v : Fin 25) : Bool :=
  Box27EarlyTerminal.entries.any (fun e => decide (e.d0 = d ∧ e.s = query d ∧ e.v = v))

def closed (d v : Fin 25) : Bool :=
  early d v || decide (d = 14 ∧ (v = 17 ∨ v = 21))

theorem d21_bound (m : Machine) (hm : Fits raw10Remainder[27]! m)
    (hd : m (3,false) = decode 14) (hv : m (3,true) = decode 21) : WeightedBound 255 m := by
  apply (weightedBound_rename_iff 255 ef (by decide) m).mp
  apply Box27D17Parent.bound255 (renameTable ef m) (fits_renamed m hm)
  · change (m (3,false)).map (renameMove ef) = _
    rw [hd,ef_code_decode]
    rfl
  · change (m (3,true)).map (renameMove ef) = _
    rw [hv,ef_code_decode]
    rfl

theorem closed_bound (d v : Fin 25) (m : Machine) (hm : child d v m)
    (hc : closed d v = true) : WeightedBound 255 m := by
  rcases hm with ⟨hf,hd,hv⟩
  rcases Bool.or_eq_true_iff.mp hc with h | h
  · obtain ⟨e,he,hh⟩ := List.any_eq_true.mp h
    obtain ⟨hed,hes,hev⟩ := of_decide_eq_true hh
    apply Box27EarlyTerminal.source_bound e he m hf
    · rw [hed]; exact hd
    · rw [hes,hev]; exact hv
  · obtain ⟨hd0,hv0⟩ := of_decide_eq_true h
    subst d
    change m (3,true) = decode v at hv
    rcases hv0 with h17 | h21
    · subst v; exact Box27D17Parent.bound255 m hf hd hv
    · subst v; exact d21_bound m hf hd hv

def pending (d v : Fin 25) : Bool :=
  decide (d ∈ sourceD0 ∧ d ∉ Box27D0FastPumps.fastCodes) && !closed d v

def canonical (d v : Fin 25) : Bool :=
  pending d v && decide (d.val ≤ 20 ∧ (16 < d.val ∨ v.val ≤ 20))

def closedKeys : List (Fin 25 × Fin 25) :=
  sourceD0.flatMap (fun d => if d ∈ Box27D0FastPumps.fastCodes then []
    else (List.finRange 25).filterMap fun v => if closed d v then some (d,v) else none)

def pendingKeys : List (Fin 25 × Fin 25) :=
  sourceD0.flatMap (fun d => (List.finRange 25).filterMap fun v =>
    if pending d v then some (d,v) else none)

def canonicalKeys : List (Fin 25 × Fin 25) :=
  sourceD0.flatMap (fun d => (List.finRange 25).filterMap fun v =>
    if canonical d v then some (d,v) else none)

theorem closedCount : closedKeys.length = 139 := by decide
theorem pendingCount : pendingKeys.length = 211 := by decide
theorem canonicalCount : canonicalKeys.length = 128 := by decide

theorem orbit_representative (d v : Fin 25) (hp : pending d v = true) :
    canonical d v = true ∨ canonical (efCode d) (efCode v) = true := by
  revert d v
  decide

theorem query_rename (d : Fin 25) :
    (ef.backward (slot (query (efCode d))).1,(slot (query (efCode d))).2) = slot (query d) := by
  revert d
  decide

theorem child_rename (d v : Fin 25) (m : Machine) (hm : child d v m) :
    child (efCode d) (efCode v) (renameTable ef m) := by
  rcases hm with ⟨hf,hd,hv⟩
  refine ⟨fits_renamed m hf,?_,?_⟩
  · change (m (3,false)).map (renameMove ef) = _
    rw [hd,ef_code_decode]
  · change (m (ef.backward (slot (query (efCode d))).1,(slot (query (efCode d))).2)).map (renameMove ef) = _
    rw [query_rename,hv,ef_code_decode]

/-- Complete original Box27 bound reduces to 128 representative child obligations.
All omitted physical children either have a source proof or are E/F conjugates. -/
theorem cover_of_canonical (B : Nat) (hB : 255 ≤ B)
    (h : ∀ d v : Fin 25, canonical d v = true → ∀ m, child d v m → WeightedBound B m) :
    ∀ m, Fits raw10Remainder[27]! m → WeightedBound B m := by
  intro m hm
  have hsrc := hm (3,false)
  rw [sourceD0eq] at hsrc
  obtain ⟨d,hd,hdv⟩ := List.mem_map.mp hsrc
  have hd0 : m (3,false) = decode d := hdv.symm
  by_cases hfast : d ∈ Box27D0FastPumps.fastCodes
  · intro k e hk he
    exact Nat.le_trans (Box27D0FastPumps.source_fast_bound m hm d hd0 hfast k e hk he) hB
  · obtain ⟨v,hv⟩ := decode_surjective (m (slot (query d)))
    have hc : child d v m := ⟨hm,hd0,hv.symm⟩
    by_cases hclosed : closed d v = true
    · intro k e hk he
      exact Nat.le_trans (closed_bound d v m hc hclosed k e hk he) hB
    · have hp : pending d v = true := by simp [pending,hd,hfast,hclosed]
      rcases orbit_representative d v hp with hr | hr
      · exact h d v hr m hc
      · exact (weightedBound_rename_iff B ef (by decide) m).mp
          (h (efCode d) (efCode v) hr (renameTable ef m) (child_rename d v m hc))

theorem cover_iff_canonical (B : Nat) (hB : 255 ≤ B) :
    (∀ m, Fits raw10Remainder[27]! m → WeightedBound B m) ↔
    (∀ d v : Fin 25, canonical d v = true → ∀ m, child d v m → WeightedBound B m) := by
  constructor
  · intro h d v hc m hm; exact h m hm.1
  · exact cover_of_canonical B hB

#print axioms d21_bound
#print axioms closed_bound
#print axioms canonicalCount
#print axioms cover_iff_canonical
end BB6.Agent49.Box27CanonicalFrontier
