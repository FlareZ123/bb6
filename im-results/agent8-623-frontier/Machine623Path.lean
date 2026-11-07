import PhysicalTraceAudit

namespace BB6Coverage

set_option maxRecDepth 12000
set_option maxHeartbeats 0

/-- Original #623 raw table, pinned rooted string
    1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA.
    No acceleration assumption is used by this file. -/
def machine623 : Machine := fun (s, b) =>
  match s.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨false, false, ⟨4, by decide⟩⟩
  | 1, false => some ⟨false, true, ⟨2, by decide⟩⟩
  | 1, true => some ⟨true, true, ⟨2, by decide⟩⟩
  | 2, false => some ⟨false, true, ⟨3, by decide⟩⟩
  | 2, true => some ⟨true, false, ⟨0, by decide⟩⟩
  | 3, false => some ⟨true, false, ⟨3, by decide⟩⟩
  | 3, true => some ⟨false, false, ⟨0, by decide⟩⟩
  | 4, false => some ⟨true, false, ⟨5, by decide⟩⟩
  | 4, true => some ⟨true, false, ⟨2, by decide⟩⟩
  | 5, false => none
  | 5, true => some ⟨false, false, ⟨0, by decide⟩⟩
  | _, _ => none

/-- Distinct state/symbol inputs in first-visit order on the *physical*
    all-zero tape. Only F/0 is not encountered in this finite prefix. -/
def machine623Visited : List Slot :=
  [(⟨0, by decide⟩, false), (⟨1, by decide⟩, false),
   (⟨2, by decide⟩, false), (⟨3, by decide⟩, false),
   (⟨3, by decide⟩, true), (⟨2, by decide⟩, true),
   (⟨1, by decide⟩, true), (⟨0, by decide⟩, true),
   (⟨4, by decide⟩, true), (⟨4, by decide⟩, false),
   (⟨5, by decide⟩, true)]

def machine623Prefix (n : Nat) : PartialMachine :=
  (machine623Visited.take n).foldl
    (fun p s => refine p s (machine623 s)) emptyTable

theorem machine623_slots_distinct : machine623Visited.Nodup := by decide

private theorem prefix_compatible_fold623 (xs : List Slot) (p : PartialMachine)
    (h : compatible p machine623) :
    compatible (xs.foldl (fun acc s => refine acc s (machine623 s)) p) machine623 := by
  induction xs generalizing p with
  | nil => simpa using h
  | cons s ss ih =>
      simpa only [List.foldl_cons] using
        ih (refine p s (machine623 s)) (compatible_refine p machine623 s h)

theorem machine623Prefix_compatible (n : Nat) :
    compatible (machine623Prefix n) machine623 := by
  unfold machine623Prefix
  exact prefix_compatible_fold623 _ _ (empty_compatible machine623)

/-- The eleven actual first unknown inputs are certified by finite
    physical tape execution, with no hypothetical read-zero shortcut. -/
theorem machine623_first_slots :
    ((List.range 11).map (fun n =>
       firstUnknownPhysical (machine623Prefix n) 96 finiteBlank)) =
      machine623Visited.map some := by decide

theorem machine623_no_new_input_before_96 :
    firstUnknownPhysical (machine623Prefix 11) 96 finiteBlank = none := by decide

def machine623DiscoveryTimes : List Nat :=
  [0, 1, 2, 3, 6, 9, 11, 13, 14, 52, 53]

theorem machine623_discovery_times :
    (machine623DiscoveryTimes.map (fun t =>
      (finitePartialRun (machine623Prefix 11) t finiteBlank).map
        (fun c => (c.state, finiteTape c c.head)))) =
      machine623Visited.map some := by decide

theorem machine623_54_moves_fixed :
    (finitePartialRun (machine623Prefix 11) 54 finiteBlank).isSome = true := by decide

theorem machine623_halt_slot_unassigned :
    machine623Prefix 11 (⟨5, by decide⟩, false) = none := by decide

theorem machine623_prefix_mass : cylinderMass (machine623Prefix 11) = 25 := by decide

/-- Every full table that extends these eleven exact machine inputs
    shares 54 true blank-tape primitive moves, regardless of F/0. -/
theorem machine623_uniform_54 (m : Machine)
    (hm : compatible (machine623Prefix 11) m) :
    (run m 54 blank).isSome = true := by
  cases h : finitePartialRun (machine623Prefix 11) 54 finiteBlank with
  | none =>
      have hc := machine623_54_moves_fixed
      simp [h] at hc
  | some c =>
      have hraw := finitePartialRun_sound
        (machine623Prefix 11) m hm finiteBlank c 54 h
      have he : run m 54 blank = some (embedFinRay c) := by
        simpa only [embedFinRay_blank] using hraw
      simp [he]

#print axioms machine623Prefix_compatible
#print axioms machine623_first_slots
#print axioms machine623_discovery_times
#print axioms machine623_uniform_54
#print axioms machine623_prefix_mass

end BB6Coverage
