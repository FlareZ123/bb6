import SparseBlankDelay

namespace BB6.Agent16WeightedSymmetry
open BB6Coverage BB6.Agent13BlankDelay

/-- Renaming commutes with every bounded traversal of the zero-writing graph.
No terminal-endpoint hypothesis is needed. -/
theorem renamed_follow (e : StatePerm) (m : Machine) (d : Nat) (s : Fin 6) :
    follow (zeroNext (renameTable e m)) d (e.forward s) =
      (follow (zeroNext m) d s).map e.forward := by
  induction d generalizing s with
  | zero => rfl
  | succ d ih =>
    rw [follow, renamed_zeroNext, follow]
    cases h : zeroNext m s with
    | none => rfl
    | some q => exact ih q

/-- Exact membership of the entire finite delay list, not just an upper bound. -/
theorem renamed_delays_iff (e : StatePerm) (m : Machine) (t : Fin 6) (d : Nat) :
    d ∈ delays (zeroNext (renameTable e m)) (e.forward t) ↔
    d ∈ delays (zeroNext m) t := by
  simp only [delays,List.mem_filter,List.mem_range,List.any_eq_true,beq_iff_eq]
  constructor
  · rintro ⟨hd,s,hs,he⟩
    refine ⟨hd,e.backward s,by simp,?_⟩
    rw [← e.rightInverse s,renamed_follow] at he
    cases h : follow (zeroNext m) d (e.backward s) with
    | none => simp [h] at he
    | some q =>
      have hq : e.forward q = e.forward t := by simpa [h] using he
      exact congrArg some (by simpa only [e.leftInverse] using congrArg e.backward hq)
  · rintro ⟨hd,s,hs,he⟩
    refine ⟨hd,e.forward s,by simp,?_⟩
    rw [renamed_follow,he]
    rfl

/-- A root-fixing permutation preserves the complete weighted halting bound. -/
theorem weightedBound_rename_iff (B : Nat) (e : StatePerm) (h0 : e.forward 0 = 0)
    (m : Machine) : WeightedBound B (renameTable e m) ↔ WeightedBound B m := by
  have halt (k : Nat) : HaltsAfter (renameTable e m) k ↔ HaltsAfter m k := by
    have h := rename_haltsAt_iff e m 0 k
    rw [h0] at h
    exact h
  have delay (d : Nat) : d ∈ delays (zeroNext (renameTable e m)) 0 ↔ d ∈ delays (zeroNext m) 0 := by
    have h := renamed_delays_iff e m 0 d
    rw [h0] at h
    exact h
  constructor
  · intro h k d hk hd
    exact h k d ((halt k).mpr hk) ((delay d).mpr hd)
  · intro h k d hk hd
    exact h k d ((halt k).mp hk) ((delay d).mp hd)

/-- An unassigned slot remains unassigned; an assigned halt remains a halt. -/
def renamePartial (e : StatePerm) (p : PartialMachine) : PartialMachine := fun s =>
  (p (e.backward s.1,s.2)).map (fun t => t.map (renameMove e))

theorem rename_compatible (e : StatePerm) {p : PartialMachine} {m : Machine}
    (h : compatible p m) : compatible (renamePartial e p) (renameTable e m) := by
  intro s t ht
  unfold renamePartial at ht
  unfold renameTable
  cases hp : p (e.backward s.1,s.2) with
  | none => simp [hp] at ht
  | some v =>
    have ht' : v.map (renameMove e) = t := by simpa [hp] using ht
    rw [h _ v hp]
    exact ht'

/-- This one-way transport suffices to discharge a residual cylinder by a
certified representative. -/
theorem weighted_cover_transport (B : Nat) (e : StatePerm) (h0 : e.forward 0 = 0)
    {p q : PartialMachine} (he : renamePartial e p = q)
    (hq : ∀ m, compatible q m → WeightedBound B m) :
    ∀ m, compatible p m → WeightedBound B m := by
  intro m hm
  have hc := rename_compatible e hm
  rw [he] at hc
  exact (weightedBound_rename_iff B e h0 m).mp (hq _ hc)

#print axioms renamed_follow
#print axioms renamed_delays_iff
#print axioms weightedBound_rename_iff
#print axioms weighted_cover_transport
end BB6.Agent16WeightedSymmetry
