import PhysicalTraceAudit

namespace BB6Coverage

/-- Exact raw transition table of Machine C (historical holdout #39),
    RLE: 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC. -/
def machineC : Machine := fun (s, b) =>
  match s.val, b with
  | 0, false => some ⟨true, true, ⟨1, by decide⟩⟩
  | 0, true => some ⟨true, false, ⟨2, by decide⟩⟩
  | 1, false => some ⟨true, false, ⟨2, by decide⟩⟩
  | 1, true => some ⟨true, true, ⟨3, by decide⟩⟩
  | 2, false => some ⟨true, false, ⟨0, by decide⟩⟩
  | 2, true => some ⟨false, false, ⟨1, by decide⟩⟩
  | 3, false => some ⟨false, true, ⟨1, by decide⟩⟩
  | 3, true => some ⟨true, true, ⟨4, by decide⟩⟩
  | 4, false => some ⟨true, true, ⟨5, by decide⟩⟩
  | 4, true => some ⟨false, true, ⟨0, by decide⟩⟩
  | 5, false => none
  | 5, true => some ⟨false, true, ⟨2, by decide⟩⟩
  | _, _ => none

/-- The order in which the blank physical run first consults eleven
    distinct nonhalting inputs. The remaining F/0 instruction halts. -/
def machineCVisited : List Slot :=
  [(⟨0, by decide⟩, false), (⟨1, by decide⟩, false),
   (⟨2, by decide⟩, true), (⟨2, by decide⟩, false),
   (⟨1, by decide⟩, true), (⟨3, by decide⟩, true),
   (⟨4, by decide⟩, false), (⟨5, by decide⟩, true),
   (⟨3, by decide⟩, false), (⟨0, by decide⟩, true),
   (⟨4, by decide⟩, true)]

def machineCPrefix (n : Nat) : PartialMachine :=
  (machineCVisited.take n).foldl
    (fun p s => refine p s (machineC s)) emptyTable

theorem machineC_slots_distinct : machineCVisited.Nodup := by decide

private theorem prefix_compatible_fold (xs : List Slot) (p : PartialMachine)
    (h : compatible p machineC) :
    compatible (xs.foldl (fun acc s => refine acc s (machineC s)) p) machineC := by
  induction xs generalizing p with
  | nil => simpa using h
  | cons s ss ih =>
      simpa only [List.foldl_cons] using
        ih (refine p s (machineC s)) (compatible_refine p machineC s h)

theorem machineCPrefix_compatible (n : Nat) :
    compatible (machineCPrefix n) machineC := by
  unfold machineCPrefix
  exact prefix_compatible_fold _ _ (empty_compatible machineC)

/-- For n=0..10 the original physical scanner picks precisely the
    (n+1)st distinct input on Machine C's blank run. -/
theorem machineC_first_slots :
    ((List.range 11).map (fun n =>
       firstUnknownPhysical (machineCPrefix n) 24 finiteBlank)) =
      machineCVisited.map some := by decide

theorem machineC_blank_prefix_no_other_input :
    firstUnknownPhysical (machineCPrefix 11) 24 finiteBlank = none := by decide

theorem machineC_first_23_moves_fixed :
    (finitePartialRun (machineCPrefix 11) 23 finiteBlank).isSome = true := by decide

def machineCDiscoveryTimes : List Nat :=
  [0, 1, 2, 4, 6, 7, 8, 9, 13, 16, 22]

theorem machineC_discovery_times :
    (machineCDiscoveryTimes.map (fun t =>
      (finitePartialRun (machineCPrefix 11) t finiteBlank).map
        (fun c => (c.state, finiteTape c c.head)))) =
      machineCVisited.map some := by decide

/-- Eleven fixed rows and one free F/0 row; exactly 25 completions. -/
theorem machineCPrefix_mass : cylinderMass (machineCPrefix 11) = 25 := by decide

/-- Every full completion of these eleven rows shares the actual first
    23 physical moves, irrespective of its eventual F/0 transition. -/
theorem machineCPrefix_uniform_23 (m : Machine)
    (hm : compatible (machineCPrefix 11) m) :
    (run m 23 blank).isSome = true := by
  cases h : finitePartialRun (machineCPrefix 11) 23 finiteBlank with
  | none =>
      have hc := machineC_first_23_moves_fixed
      simp [h] at hc
  | some c =>
      have hraw := finitePartialRun_sound
        (machineCPrefix 11) m hm finiteBlank c 23 h
      have he : run m 23 blank = some (embedFinRay c) := by
        simpa only [embedFinRay_blank] using hraw
      simp [he]

theorem machineC_halt_slot_unassigned :
    machineCPrefix 11 (⟨5, by decide⟩, false) = none := by decide

#print axioms machineCPrefix_compatible
#print axioms machineC_first_slots
#print axioms machineC_discovery_times
#print axioms machineCPrefix_uniform_23
#print axioms machineCPrefix_mass

end BB6Coverage
