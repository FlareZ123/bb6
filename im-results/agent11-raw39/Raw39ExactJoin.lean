import Raw39AcceptedNine
import Raw391LELateWeight
import Raw390LELateWeight
import Raw391LEBoundLift

namespace BB6.Agent43Raw39ExactJoin
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent11SemanticChunks
open BB6.Agent11Raw39AcceptedSix (p39 child)
open BB6.Agent43Raw391LEBoundLift (mono)
open BB6.Agent10ZipAudit
open BB6.Agent43Raw391LELate (table)

theorem parent_not_bound : ¬ Bound 28310 p39 := by
  intro h
  apply BB6.Agent43Raw391LELate.parent_not_bound
  intro m hm
  exact h m (refine_preserves_compat p39 m (0,true) (some ⟨true,false,4⟩) (by decide) hm)

theorem parent_bound (h0 : Bound 15125 (child ⟨false,false,4⟩))
    (h1 : Bound 28311 (child ⟨true,false,4⟩)) : Bound 28311 p39 := by
  apply BB6.Agent11Raw39AcceptedNine.parent_bound_two 28311 (by decide)
  intro mv hm
  simp only [BB6.Agent11Raw39AcceptedNine.remaining, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact mono (by decide : 15125 ≤ 28311) h0
  · exact h1

theorem parent_cover (h0 : Bound 15125 (child ⟨false,false,4⟩))
    (h1 : Bound 28311 (child ⟨true,false,4⟩)) : Cover (WeightedBound 28311) p39 :=
  .leaf p39 (parent_bound h0 h1)

theorem parent_exact (h0 : Bound 15125 (child ⟨false,false,4⟩))
    (h1 : Bound 28311 (child ⟨true,false,4⟩)) (B : Nat) :
    Bound B p39 ↔ 28311 ≤ B := by
  constructor
  · intro h
    by_cases hc : 28311 ≤ B
    · exact hc
    · exact False.elim (parent_not_bound (mono (by omega : B ≤ 28310) h))
  · intro h
    exact mono h (parent_bound h0 h1)

theorem zeroLE_exact (h0 : Bound 15125 (child ⟨false,false,4⟩)) (B : Nat) :
    Bound B (child ⟨false,false,4⟩) ↔ 15125 ≤ B := by
  constructor
  · intro h
    by_cases hc : 15125 ≤ B
    · exact hc
    · exact False.elim (BB6.Agent43Raw390LELate.parent_not_bound (mono (by omega : B ≤ 15124) h))
  · intro h
    exact mono h h0

theorem oneLE_exact (h1 : Bound 28311 (child ⟨true,false,4⟩)) (B : Nat) :
    Bound B (child ⟨true,false,4⟩) ↔ 28311 ≤ B := by
  constructor
  · intro h
    by_cases hc : 28311 ≤ B
    · exact hc
    · exact False.elim (BB6.Agent43Raw391LELate.parent_not_bound (mono (by omega : B ≤ 28310) h))
  · intro h
    exact mono h h1

/-- The explicit halting completion of the late 1LE leaf. -/
def witness : Machine := fun s => (table s).getD none

theorem witness_compatible : compatible (refine table (5,false) none) witness := by
  intro s t ht
  by_cases hs : s = (5,false)
  · subst s
    simp [refine] at ht
    subst t
    rfl
  · have he : table s = some t := by simpa [refine,hs] using ht
    simp [witness,he]

theorem witness_time : HaltsAfter witness 28309 := by
  obtain ⟨hr,hu,_⟩ := zipQueryOK_sound BB6.Agent43Raw391LELate.query
  cases h : knownRun table 28309 with
  | none => simp [h] at hr
  | some c =>
    have hs : readSlot c = (5,false) := by simpa [h] using hr
    exact first_hole_halts table 28309 c h (by simpa [hs] using hu) witness
      (by simpa [hs] using witness_compatible)

theorem witness_delay : 1 ∈ delays (zeroNext witness) 0 := by decide

theorem witness_parent : compatible p39 witness := by
  intro s t hs
  apply witness_compatible s t
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> first | exact hs | contradiction

theorem parent_attained : ∃ m k d, compatible p39 m ∧ HaltsAfter m k ∧
    d ∈ delays (zeroNext m) 0 ∧ d+k+1 = 28311 :=
  ⟨witness,28309,1,witness_parent,witness_time,witness_delay,by decide⟩

#print axioms zeroLE_exact
#print axioms oneLE_exact
#print axioms parent_attained
#print axioms parent_not_bound
#print axioms parent_bound
#print axioms parent_cover
#print axioms parent_exact
end BB6.Agent43Raw39ExactJoin
