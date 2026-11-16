import ResidualFrontierManifest
import MachineCFrontier
import Machine623Frontier

namespace BB6Coverage

set_option maxRecDepth 12000
set_option maxHeartbeats 0

/-- Follow the actual transition chosen by a total machine through an audit,
recording the exact ordered branch path. -/
def FrontierAudit.selectedPath {good : Machine → Prop} {p : PartialMachine} :
    FrontierAudit good p → Machine → List (Slot × Transition) →
      List (Slot × Transition)
  | .certified _ _, _, path => path
  | .unresolved _, _, path => path
  | .branch _ slot _ children, m, path =>
      (children (m slot) (choices_complete (m slot))).selectedPath
        m (path ++ [(slot, m slot)])

/-- The exact partial table reached by following a machine through an audit. -/
def FrontierAudit.selectedPartial {good : Machine → Prop} {p : PartialMachine} :
    FrontierAudit good p → Machine → PartialMachine
  | .certified p _, _ => p
  | .unresolved p, _ => p
  | .branch _ slot _ children, m =>
      (children (m slot) (choices_complete (m slot))).selectedPartial m

/-- Appending one actual branch decision to a path performs exactly one
    `refine` on the partial table reconstructed from that path. -/
theorem partialOfPath_append_single (path : List (Slot × Transition))
    (slot : Slot) (t : Transition) :
    partialOfPath (path ++ [(slot,t)]) =
      refine (partialOfPath path) slot t := by
  simp [partialOfPath, List.foldl_append]

/-- The selected audit partial table is exactly the table reconstructed
    from its selected ordered path. -/
theorem FrontierAudit.selectedPartial_eq_path
    {good : Machine → Prop} {p : PartialMachine}
    (audit : FrontierAudit good p) (m : Machine)
    (path : List (Slot × Transition))
    (hstart : p = partialOfPath path) :
    audit.selectedPartial m = partialOfPath (audit.selectedPath m path) := by
  induction audit generalizing path with
  | certified p proof =>
      simpa [FrontierAudit.selectedPartial, FrontierAudit.selectedPath] using hstart
  | unresolved p =>
      simpa [FrontierAudit.selectedPartial, FrontierAudit.selectedPath] using hstart
  | branch p slot fresh children ih =>
      have hchild :
          refine p slot (m slot) =
            partialOfPath (path ++ [(slot, m slot)]) := by
        calc
          refine p slot (m slot) =
              refine (partialOfPath path) slot (m slot) := by rw [hstart]
          _ = partialOfPath (path ++ [(slot, m slot)]) :=
            (partialOfPath_append_single path slot (m slot)).symm
      exact ih (m slot) (choices_complete (m slot))
        (path ++ [(slot, m slot)]) hchild

/-- An open leaf has a concrete manifest terminal with the exact selected
    path, its source-table match, and the exact weight of its partial table. -/
theorem FrontierAudit.open_has_exact_terminal
    {good : Machine → Prop} {p : PartialMachine}
    (audit : FrontierAudit good p) (m : Machine)
    (path : List (Slot × Transition))
    (hpath : ∀ s t, (s,t) ∈ path → m s = t)
    (hopen : audit.open m) :
    ∃ term, term ∈ audit.terminals path ∧
      term.path = audit.selectedPath m path ∧
      term.certified = false ∧
      term.matches m ∧
      term.weight = cylinderMass (audit.selectedPartial m) := by
  induction audit generalizing path with
  | certified p proof =>
      simp [FrontierAudit.open] at hopen
  | unresolved p =>
      refine ⟨⟨path, false, cylinderMass p⟩, ?_, ?_, rfl, hpath, ?_⟩
      · simp [FrontierAudit.terminals]
      · simp [FrontierAudit.selectedPath]
      · simp [FrontierAudit.selectedPartial]
  | branch p slot fresh children ih =>
      have hchild :
          (children (m slot) (choices_complete (m slot))).open m := by
        simpa [FrontierAudit.open] using hopen
      have hpath' :
          ∀ s t, (s,t) ∈ path ++ [(slot, m slot)] → m s = t := by
        intro s t h
        rcases List.mem_append.mp h with h | h
        · exact hpath s t h
        · have he : (s,t) = (slot, m slot) := by simpa using h
          cases he
          rfl
      obtain ⟨term, hmem, hselected, hcert, hmatches, hweight⟩ :=
        ih (m slot) (choices_complete (m slot))
          (path ++ [(slot, m slot)]) hpath' hchild
      refine ⟨term, ?_, ?_, hcert, hmatches, ?_⟩
      · simp only [FrontierAudit.terminals]
        exact List.mem_flatMap.mpr ⟨⟨m slot, choices_complete (m slot)⟩,
          by simp, hmem⟩
      · simpa [FrontierAudit.selectedPath] using hselected
      · simpa [FrontierAudit.selectedPartial] using hweight

/-- The four exact branch decisions by which the global audit reaches
    Machine C's authentic physical blank-root path. -/
def machineCDepthFourPath : List (Slot × Transition) :=
  (machineCVisited.take 4).map (fun s => (s, machineC s))

/-- The four exact branch decisions by which the global audit reaches
    #623's authentic physical blank-root path. -/
def machine623DepthFourPath : List (Slot × Transition) :=
  (machine623Visited.take 4).map (fun s => (s, machine623 s))

theorem machineC_selected_path :
    depth4ResidualAudit.selectedPath machineC [] =
      machineCDepthFourPath := by
  decide

theorem machine623_selected_path :
    depth4ResidualAudit.selectedPath machine623 [] =
      machine623DepthFourPath := by
  decide

theorem machineC_selected_partial_path :
    depth4ResidualAudit.selectedPartial machineC =
      partialOfPath machineCDepthFourPath := by
  have h := FrontierAudit.selectedPartial_eq_path
    depth4ResidualAudit machineC [] rfl
  simpa [machineC_selected_path] using h

theorem machine623_selected_partial_path :
    depth4ResidualAudit.selectedPartial machine623 =
      partialOfPath machine623DepthFourPath := by
  have h := FrontierAudit.selectedPartial_eq_path
    depth4ResidualAudit machine623 [] rfl
  simpa [machine623_selected_path] using h

/-- Any finite path whose entries agree with a total machine defines
    a partial table compatible with that machine. -/
private theorem foldRefineCompatible (xs : List (Slot × Transition))
    (p : PartialMachine) (m : Machine)
    (hp : compatible p m)
    (hxs : ∀ s t, (s,t) ∈ xs → m s = t) :
    compatible (xs.foldl (fun acc entry => refine acc entry.1 entry.2) p) m := by
  induction xs generalizing p with
  | nil =>
      simpa using hp
  | cons entry xs ih =>
      rcases entry with ⟨slot, trans⟩
      have htrans : m slot = trans := hxs slot trans (by simp)
      have hchild : compatible (refine p slot trans) m := by
        rw [← htrans]
        exact compatible_refine p m slot hp
      apply ih (refine p slot trans) hchild
      intro s t hmem
      exact hxs s t (by simp [hmem])

theorem partialOfPath_compatible (path : List (Slot × Transition))
    (m : Machine) (hpath : ∀ s t, (s,t) ∈ path → m s = t) :
    compatible (partialOfPath path) m := by
  unfold partialOfPath
  exact foldRefineCompatible path emptyTable m (empty_compatible m) hpath

/-- The authentic eleven-row source cylinders lie inside the corresponding
    four-row manifest cylinders. -/
theorem machineC_path_in_source_prefix :
    ∀ s t, (s,t) ∈ machineCDepthFourPath →
      machineCPrefix 11 s = some t := by
  decide

theorem machine623_path_in_source_prefix :
    ∀ s t, (s,t) ∈ machine623DepthFourPath →
      machine623Prefix 11 s = some t := by
  decide

theorem machineC_authentic_cylinder_inside_manifest_leaf (m : Machine)
    (hm : compatible (machineCPrefix 11) m) :
    compatible (partialOfPath machineCDepthFourPath) m := by
  apply partialOfPath_compatible
  intro s t h
  exact hm s t (machineC_path_in_source_prefix s t h)

theorem machine623_authentic_cylinder_inside_manifest_leaf (m : Machine)
    (hm : compatible (machine623Prefix 11) m) :
    compatible (partialOfPath machine623DepthFourPath) m := by
  apply partialOfPath_compatible
  intro s t h
  exact hm s t (machine623_path_in_source_prefix s t h)

theorem machineC_manifest_path_length :
    machineCDepthFourPath.length = 4 := by decide

theorem machine623_manifest_path_length :
    machine623DepthFourPath.length = 4 := by decide

theorem machineC_manifest_oracles_false :
    finiteDecisionOracle (partialOfPath machineCDepthFourPath) 6 6 = false ∧
    finiteLassoOracle (partialOfPath machineCDepthFourPath) 12 = false ∧
    finiteEntryMacroBiOracle (partialOfPath machineCDepthFourPath) 2 4 = false := by
  decide

theorem machine623_manifest_oracles_false :
    finiteDecisionOracle (partialOfPath machine623DepthFourPath) 6 6 = false ∧
    finiteLassoOracle (partialOfPath machine623DepthFourPath) 12 = false ∧
    finiteEntryMacroBiOracle (partialOfPath machine623DepthFourPath) 2 4 = false := by
  decide

/-- Machine C is matched by this exact open terminal path; the existing
    manifest uniqueness theorem makes it the root's unique matching terminal.
    The terminal weight is the exact 25^8 completion mass. -/
theorem machineC_manifest_terminal :
    ∃ term : AuditTerminal, term ∈ depth4ResidualTerminals ∧
      term.path = machineCDepthFourPath ∧
      term.certified = false ∧ term.weight = 25^8 ∧
      term.matches machineC := by
  have hopen : depth4ResidualAudit.open machineC := by
    simpa [depth4ResidualAudit] using machineC_depth_four_open
  obtain ⟨term, hmem, hpath, hcert, hmatches, hweight⟩ :=
    FrontierAudit.open_has_exact_terminal
      depth4ResidualAudit machineC [] (by simp) hopen
  refine ⟨term, ?_, ?_, hcert, ?_, hmatches⟩
  · simpa [depth4ResidualTerminals] using hmem
  · simpa [machineC_selected_path] using hpath
  · calc
      term.weight =
          cylinderMass (depth4ResidualAudit.selectedPartial machineC) := hweight
      _ = cylinderMass (partialOfPath machineCDepthFourPath) := by
        rw [machineC_selected_partial_path]
      _ = 25^8 := by decide

/-- #623 is matched by this exact open terminal path; the existing manifest
    uniqueness theorem makes it the root's unique matching terminal.
    The terminal weight is the exact 25^8 completion mass. -/
theorem machine623_manifest_terminal :
    ∃ term : AuditTerminal, term ∈ depth4ResidualTerminals ∧
      term.path = machine623DepthFourPath ∧
      term.certified = false ∧ term.weight = 25^8 ∧
      term.matches machine623 := by
  have hopen : depth4ResidualAudit.open machine623 := by
    simpa [depth4ResidualAudit] using machine623_depth_four_open
  obtain ⟨term, hmem, hpath, hcert, hmatches, hweight⟩ :=
    FrontierAudit.open_has_exact_terminal
      depth4ResidualAudit machine623 [] (by simp) hopen
  refine ⟨term, ?_, ?_, hcert, ?_, hmatches⟩
  · simpa [depth4ResidualTerminals] using hmem
  · simpa [machine623_selected_path] using hpath
  · calc
      term.weight =
          cylinderMass (depth4ResidualAudit.selectedPartial machine623) := hweight
      _ = cylinderMass (partialOfPath machine623DepthFourPath) := by
        rw [machine623_selected_partial_path]
      _ = 25^8 := by decide

def machineCProbeEndpoint : FinRayCfg :=
  { state := ⟨1, by decide⟩, head := -2, ones := [-3, -2, -1, 1] }

def machineCProbeSlot : Slot := (⟨1, by decide⟩, true)

def machine623ProbeEndpoint : FinRayCfg :=
  { state := ⟨3, by decide⟩, head := 0, ones := [1, 2, 3, 0] }

def machine623ProbeSlot : Slot := (⟨3, by decide⟩, true)

/-- After its four manifest rows, Machine C's first still-free physical
    input is B/1, consulted after six successful moves. -/
theorem machineC_manifest_probe :
    physicalScanProbe (partialOfPath machineCDepthFourPath) 12 0 finiteBlank =
      .unknown 6 machineCProbeEndpoint machineCProbeSlot := by
  decide

/-- After its four manifest rows, #623's first still-free physical input
    is D/1, consulted after six successful moves. -/
theorem machine623_manifest_probe :
    physicalScanProbe (partialOfPath machine623DepthFourPath) 12 0 finiteBlank =
      .unknown 6 machine623ProbeEndpoint machine623ProbeSlot := by
  decide

/-- Every full table in Machine C's exact depth-four manifest cylinder
    shares the six-move prefix and leaves B/1 as the next free input. -/
theorem machineC_manifest_probe_uniform (m : Machine)
    (hm : compatible (partialOfPath machineCDepthFourPath) m) :
    run m 6 blank = some (embedFinRay machineCProbeEndpoint) ∧
      machineCProbeSlot =
        (machineCProbeEndpoint.state,
          finiteTape machineCProbeEndpoint machineCProbeEndpoint.head) ∧
      (partialOfPath machineCDepthFourPath) machineCProbeSlot = none := by
  obtain ⟨moves, hmoves, hsteps, hrun, hslot, hfree⟩ :=
    physicalScanProbe_unknown_exact
      (partialOfPath machineCDepthFourPath) 12 0 finiteBlank 6
      machineCProbeEndpoint machineCProbeSlot machineC_manifest_probe
  have hmovesEq : moves = 6 := by omega
  subst moves
  have hraw := finitePartialRun_sound
    (partialOfPath machineCDepthFourPath) m hm finiteBlank
      machineCProbeEndpoint 6 hrun
  exact ⟨by simpa only [embedFinRay_blank] using hraw, hslot, hfree⟩

/-- Every full table in #623's exact depth-four manifest cylinder shares
    the six-move prefix and leaves D/1 as the next free input. -/
theorem machine623_manifest_probe_uniform (m : Machine)
    (hm : compatible (partialOfPath machine623DepthFourPath) m) :
    run m 6 blank = some (embedFinRay machine623ProbeEndpoint) ∧
      machine623ProbeSlot =
        (machine623ProbeEndpoint.state,
          finiteTape machine623ProbeEndpoint machine623ProbeEndpoint.head) ∧
      (partialOfPath machine623DepthFourPath) machine623ProbeSlot = none := by
  obtain ⟨moves, hmoves, hsteps, hrun, hslot, hfree⟩ :=
    physicalScanProbe_unknown_exact
      (partialOfPath machine623DepthFourPath) 12 0 finiteBlank 6
      machine623ProbeEndpoint machine623ProbeSlot machine623_manifest_probe
  have hmovesEq : moves = 6 := by omega
  subst moves
  have hraw := finitePartialRun_sound
    (partialOfPath machine623DepthFourPath) m hm finiteBlank
      machine623ProbeEndpoint 6 hrun
  exact ⟨by simpa only [embedFinRay_blank] using hraw, hslot, hfree⟩

#print axioms FrontierAudit.selectedPartial_eq_path
#print axioms FrontierAudit.open_has_exact_terminal
#print axioms machineC_manifest_terminal
#print axioms machine623_manifest_terminal
#print axioms partialOfPath_compatible
#print axioms machineC_authentic_cylinder_inside_manifest_leaf
#print axioms machine623_authentic_cylinder_inside_manifest_leaf
#print axioms machineC_manifest_oracles_false
#print axioms machine623_manifest_oracles_false
#print axioms machineC_manifest_probe
#print axioms machine623_manifest_probe
#print axioms machineC_manifest_probe_uniform
#print axioms machine623_manifest_probe_uniform

end BB6Coverage
