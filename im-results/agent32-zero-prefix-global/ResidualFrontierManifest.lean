import LassoTraceAudit
import FrontierUnique
import FrontierManifestMass

namespace BB6Coverage

set_option maxRecDepth 12000
set_option maxHeartbeats 0

/-- The exact depth-four audit used for the reported 68.066560% frontier.
    The parameters are: score bound 6, finite-ray limit 6, physical scan
    limit 12, exact-lasso limit 12, entry-prefix limit 2, macro limit 4. -/
def depth4ResidualAudit : FrontierAudit (DecidedBelow 6) emptyTable :=
  lassoPhysicalTraceAudit emptyTable 6 6 12 12 2 4 4

/-- A complete, ordered manifest of every terminal cylinder in the audit.
    Each terminal records its actual sequence of fresh slot assignments,
    whether that cylinder is source-certified or unresolved, and its exact
    number of compatible raw full tables. -/
def depth4ResidualTerminals : List AuditTerminal :=
  depth4ResidualAudit.terminals

/-- Every full raw table has one and only one manifest terminal. -/
theorem depth4ResidualManifest_unique (m : Machine) :
    ∃ term : AuditTerminal, term ∈ depth4ResidualTerminals ∧
      term.matches m ∧
      (∀ other : AuditTerminal, other ∈ depth4ResidualTerminals →
        other.matches m → other = term) := by
  exact depth4ResidualAudit.unique_actual_terminal m (empty_compatible m)

/-- The terminal manifest retains the exact certified mass of the audit. -/
theorem depth4ResidualManifest_certifiedMass :
    (depth4ResidualTerminals.map AuditTerminal.certMass).sum =
      depth4ResidualAudit.report.1 := by
  exact depth4ResidualAudit.terminals_certMass []

/-- The terminal manifest retains the exact unresolved mass of the audit. -/
theorem depth4ResidualManifest_openMass :
    (depth4ResidualTerminals.map AuditTerminal.openMass).sum =
      depth4ResidualAudit.report.2 := by
  exact depth4ResidualAudit.terminals_openMass []

/-- Certified and unresolved terminal cylinders partition all 25^12 tables. -/
theorem depth4ResidualManifest_totalMass :
    (depth4ResidualTerminals.map AuditTerminal.certMass).sum +
      (depth4ResidualTerminals.map AuditTerminal.openMass).sum = 25^12 := by
  rw [depth4ResidualManifest_certifiedMass, depth4ResidualManifest_openMass]
  calc
    _ = cylinderMass emptyTable := depth4ResidualAudit.report_conserves
    _ = 25^12 := by decide

/-- The exact all-table decision boundary remains visible in the manifest. -/
theorem depth4ResidualManifest_exhaustive (m : Machine) :
    DecidedBelow 6 m ∨ depth4ResidualAudit.open m :=
  depth4ResidualAudit.exhaustive m (empty_compatible m)

def encodeBit (b : Bool) : String := if b then "1" else "0"

def encodeTransition (t : Transition) : String :=
  match t with
  | none => "H"
  | some mv =>
      "M" ++ encodeBit mv.write ++ encodeBit mv.right ++ toString mv.next.val

def encodeSlot (slot : Slot) : String :=
  toString slot.1.val ++ encodeBit slot.2

def encodeEntry (entry : Slot × Transition) : String :=
  encodeSlot entry.1 ++ ":" ++ encodeTransition entry.2

def encodePath (path : List (Slot × Transition)) : String :=
  String.intercalate "," (path.map encodeEntry)

/-- Reconstruct the exact partial table represented by a terminal path. -/
def partialOfPath (path : List (Slot × Transition)) : PartialMachine :=
  path.foldl (fun p entry => refine p entry.1 entry.2) emptyTable

/-- A diagnostic execution of the same physical scan used to choose audit
    branches. It distinguishes a next free input, an assigned halt, and the
    12-move scan limit, while retaining the exact physical configuration. -/
inductive PhysicalScanProbe where
  | unknown (successfulMoves : Nat) (cfg : FinRayCfg) (slot : Slot)
  | halt (successfulMoves : Nat) (cfg : FinRayCfg)
  | limit (successfulMoves : Nat) (cfg : FinRayCfg)

def physicalScanProbe (p : PartialMachine) :
    Nat → Nat → FinRayCfg → PhysicalScanProbe
  | 0, successfulMoves, cfg => .limit successfulMoves cfg
  | n+1, successfulMoves, cfg =>
      match p (cfg.state, finiteTape cfg cfg.head) with
      | none => .unknown successfulMoves cfg (cfg.state, finiteTape cfg cfg.head)
      | some none => .halt successfulMoves cfg
      | some (some mv) =>
          physicalScanProbe p n (successfulMoves+1) (finiteMove cfg mv)

/-- An unknown probe is exactly the slot selected by the original
    firstUnknownPhysical branch policy. -/
theorem physicalScanProbe_unknown_matches (p : PartialMachine)
    (n successfulMoves : Nat) (cfg : FinRayCfg) (k : Nat)
    (d : FinRayCfg) (slot : Slot)
    (h : physicalScanProbe p n successfulMoves cfg =
      .unknown k d slot) :
    firstUnknownPhysical p n cfg = some slot := by
  induction n generalizing successfulMoves cfg k d with
  | zero =>
      simp [physicalScanProbe] at h
  | succ n ih =>
      cases hp : p (cfg.state, finiteTape cfg cfg.head) with
      | none =>
          rcases (by simpa [physicalScanProbe, hp] using h) with
            ⟨_, ⟨_, hslot⟩⟩
          simp only [firstUnknownPhysical, hp]
          exact congrArg some hslot
      | some trans =>
          cases trans with
          | none =>
              simp [physicalScanProbe, hp] at h
          | some mv =>
              have hnext :
                  physicalScanProbe p n (successfulMoves+1)
                    (finiteMove cfg mv) = .unknown k d slot := by
                simpa [physicalScanProbe, hp] using h
              have hscan := ih (successfulMoves+1) (finiteMove cfg mv) k d hnext
              simpa [firstUnknownPhysical, hp] using hscan

/-- Every unknown probe records an exact finite prefix of successful moves,
    and the selected slot is genuinely unassigned at its endpoint. -/
theorem physicalScanProbe_unknown_exact (p : PartialMachine) :
    ∀ n successfulMoves cfg k d slot,
      physicalScanProbe p n successfulMoves cfg = .unknown k d slot →
      ∃ moves, moves < n ∧ k = successfulMoves + moves ∧
        finitePartialRun p moves cfg = some d ∧
        slot = (d.state, finiteTape d d.head) ∧ p slot = none := by
  intro n
  induction n with
  | zero =>
      intro successfulMoves cfg k d slot h
      simp [physicalScanProbe] at h
  | succ n ih =>
      intro successfulMoves cfg k d slot h
      cases hp : p (cfg.state, finiteTape cfg cfg.head) with
      | none =>
          rcases (by simpa [physicalScanProbe, hp] using h) with
            ⟨hk, ⟨hd, hslot⟩⟩
          subst k
          subst d
          subst slot
          refine ⟨0, by omega, by omega, ?_, rfl, hp⟩
          simp [finitePartialRun]
      | some trans =>
          cases trans with
          | none =>
              simp [physicalScanProbe, hp] at h
          | some mv =>
              have hnext :
                  physicalScanProbe p n (successfulMoves+1)
                    (finiteMove cfg mv) = .unknown k d slot := by
                simpa [physicalScanProbe, hp] using h
              obtain ⟨moves, hlt, hk, hrun, hslot, hfree⟩ :=
                ih (successfulMoves+1) (finiteMove cfg mv) k d slot hnext
              refine ⟨moves+1, ?_, ?_, ?_, hslot, hfree⟩
              · omega
              · omega
              · rw [finitePartialRun_one_prefix p cfg mv hp moves]
                exact hrun

/-- A halt probe records the exact number of successful moves before the
    assigned undefined transition is queried. -/
theorem physicalScanProbe_halt_exact (p : PartialMachine) :
    ∀ n successfulMoves cfg k d,
      physicalScanProbe p n successfulMoves cfg = .halt k d →
      ∃ moves, moves ≤ n ∧ k = successfulMoves + moves ∧
        finitePartialRun p moves cfg = some d ∧
        p (d.state, finiteTape d d.head) = some none := by
  intro n
  induction n with
  | zero =>
      intro successfulMoves cfg k d h
      simp [physicalScanProbe] at h
  | succ n ih =>
      intro successfulMoves cfg k d h
      cases hp : p (cfg.state, finiteTape cfg cfg.head) with
      | none =>
          simp [physicalScanProbe, hp] at h
      | some trans =>
          cases trans with
          | none =>
              rcases (by simpa [physicalScanProbe, hp] using h) with
                ⟨hk, hd⟩
              subst k
              subst d
              refine ⟨0, by omega, by omega, ?_, hp⟩
              simp [finitePartialRun]
          | some mv =>
              have hnext :
                  physicalScanProbe p n (successfulMoves+1)
                    (finiteMove cfg mv) = .halt k d := by
                simpa [physicalScanProbe, hp] using h
              obtain ⟨moves, hle, hk, hrun, hhalt⟩ :=
                ih (successfulMoves+1) (finiteMove cfg mv) k d hnext
              refine ⟨moves+1, ?_, ?_, ?_, hhalt⟩
              · omega
              · omega
              · rw [finitePartialRun_one_prefix p cfg mv hp moves]
                exact hrun

/-- A limit probe is an exact source-simulator prefix of the stated length. -/
theorem physicalScanProbe_limit_exact (p : PartialMachine) :
    ∀ n successfulMoves cfg k d,
      physicalScanProbe p n successfulMoves cfg = .limit k d →
      k = successfulMoves + n ∧ finitePartialRun p n cfg = some d := by
  intro n
  induction n with
  | zero =>
      intro successfulMoves cfg k d h
      rcases (by simpa [physicalScanProbe] using h) with ⟨hk, hd⟩
      subst k
      subst d
      constructor
      · omega
      · simp [finitePartialRun]
  | succ n ih =>
      intro successfulMoves cfg k d h
      cases hp : p (cfg.state, finiteTape cfg cfg.head) with
      | none =>
          simp [physicalScanProbe, hp] at h
      | some trans =>
          cases trans with
          | none =>
              simp [physicalScanProbe, hp] at h
          | some mv =>
              have hnext :
                  physicalScanProbe p n (successfulMoves+1)
                    (finiteMove cfg mv) = .limit k d := by
                simpa [physicalScanProbe, hp] using h
              obtain ⟨hk, hrun⟩ :=
                ih (successfulMoves+1) (finiteMove cfg mv) k d hnext
              constructor
              · omega
              · rw [finitePartialRun_one_prefix p cfg mv hp n]
                exact hrun

/-- A halt probe is a genuine exact-score blank-root witness for every
    completion of the terminal partial table. -/
theorem physicalScanProbe_halt_exact_for_completion
    (p : PartialMachine) (m : Machine) (hm : compatible p m)
    (scanLimit steps : Nat) (cfg : FinRayCfg)
    (h : physicalScanProbe p scanLimit 0 finiteBlank = .halt steps cfg) :
    HaltsAfter m steps := by
  obtain ⟨moves, hle, hsteps, hrun, hhalt⟩ :=
    physicalScanProbe_halt_exact p scanLimit 0 finiteBlank steps cfg h
  have hsteps' : steps = moves := by simpa using hsteps
  subst steps
  have hroot : run m moves blank = some (embedFinRay cfg) := by
    simpa only [embedFinRay_blank] using
      finitePartialRun_sound p m hm finiteBlank cfg moves hrun
  have hhaltRaw : m (readSlot (embedFinRay cfg)) = none := by
    simpa [readSlot, embedFinRay] using
      hm (cfg.state, finiteTape cfg cfg.head) none hhalt
  change (run m moves blank).isSome = true ∧
    run m (moves + 1) blank = none
  constructor
  · simp [hroot]
  · exact halting_entry m blank (embedFinRay cfg) moves hroot hhaltRaw

/-- Consequently a halt probe yields a source proof-carrying Cover leaf at
    its exact score, even when that score exceeds the audit's bound six. -/
theorem physicalScanProbe_halt_cover
    (p : PartialMachine) (scanLimit steps : Nat) (cfg : FinRayCfg)
    (h : physicalScanProbe p scanLimit 0 finiteBlank = .halt steps cfg) :
    Cover (DecidedBelow (steps+1)) p := by
  apply Cover.leaf
  intro m hm
  right
  exact ⟨steps, by omega,
    physicalScanProbe_halt_exact_for_completion p m hm scanLimit steps cfg h⟩

/-- An unknown probe is a real blank-root prefix in every compatible
    original machine, not merely a guessed control-path position. -/
theorem physicalScanProbe_unknown_is_raw_prefix
    (p : PartialMachine) (m : Machine) (hm : compatible p m)
    (scanLimit steps : Nat) (cfg : FinRayCfg) (slot : Slot)
    (h : physicalScanProbe p scanLimit 0 finiteBlank =
      .unknown steps cfg slot) :
    ∃ k, k < scanLimit ∧
      run m k blank = some (embedFinRay cfg) ∧
      slot = (cfg.state, finiteTape cfg cfg.head) ∧ p slot = none := by
  obtain ⟨moves, hlt, hsteps, hrun, hslot, hfree⟩ :=
    physicalScanProbe_unknown_exact p scanLimit 0 finiteBlank steps cfg slot h
  have hroot : run m moves blank = some (embedFinRay cfg) := by
    simpa only [embedFinRay_blank] using
      finitePartialRun_sound p m hm finiteBlank cfg moves hrun
  exact ⟨moves, hlt, hroot, hslot, hfree⟩

/-- A scan-limit probe is an exact original-machine prefix of every
    compatible completion. -/
theorem physicalScanProbe_limit_is_raw_prefix
    (p : PartialMachine) (m : Machine) (hm : compatible p m)
    (scanLimit : Nat) (cfg : FinRayCfg)
    (h : physicalScanProbe p scanLimit 0 finiteBlank =
      .limit scanLimit cfg) :
    run m scanLimit blank = some (embedFinRay cfg) := by
  obtain ⟨_, hrun⟩ :=
    physicalScanProbe_limit_exact p scanLimit 0 finiteBlank scanLimit cfg h
  simpa only [embedFinRay_blank] using
    finitePartialRun_sound p m hm finiteBlank cfg scanLimit hrun

def encodeProbeFields : PhysicalScanProbe → List String
  | .unknown successfulMoves cfg slot =>
      ["U", toString successfulMoves, toString cfg.state.val,
        toString cfg.head, String.intercalate "," (cfg.ones.map toString),
        encodeSlot slot]
  | .halt successfulMoves cfg =>
      ["H", toString successfulMoves, toString cfg.state.val,
        toString cfg.head, String.intercalate "," (cfg.ones.map toString), "-"]
  | .limit successfulMoves cfg =>
      ["L", toString successfulMoves, toString cfg.state.val,
        toString cfg.head, String.intercalate "," (cfg.ones.map toString), "-"]

/-- Each open terminal is accompanied by the failed-oracle status and a
    concrete next-step diagnostic. An open node at path depth four stopped
    only because the tree budget was exhausted; a shallower open node stopped
    because its 12-position physical scan found no unassigned input. -/
def encodeTerminal (term : AuditTerminal) : String :=
  let p := partialOfPath term.path
  let auditStop :=
    if term.certified then "source-certified"
    else if term.path.length == 4 then "tree-depth-exhausted"
    else "physical-scan-no-unassigned-input"
  let oracleOutcomes :=
    if term.certified then "accepted"
    else "finiteDecision=0,finiteLasso=0,finiteEntryMacroBi=0"
  let probeFields :=
    if term.certified then ["-", "0", "-", "0", "", "-"]
    else encodeProbeFields (physicalScanProbe p 12 0 finiteBlank)
  String.intercalate "\t"
    ([if term.certified then "C" else "O",
      toString term.weight,
      toString term.path.length,
      auditStop,
      oracleOutcomes] ++ probeFields ++
      [encodePath term.path])

/-!
The canonicalizer applies the 240 root-preserving symmetries: all 5!
permutations of B..F while fixing A, optionally composed with L/R reflection.
The source semantics of state relabelling and reflection is kernel-checked in
agent8-coverage-contract/Symmetry.lean. The external Python step exhaustively
computes the finite orbit key; it does not alter the source proof tree.
-/

#eval do
  let terms : List AuditTerminal := depth4ResidualTerminals
  let report := depth4ResidualAudit.report
  let openCount := (terms.filter
    (fun (t : AuditTerminal) => !(AuditTerminal.certified t))).length
  let certifiedCount := (terms.filter
    (fun (t : AuditTerminal) => AuditTerminal.certified t)).length
  IO.FS.writeFile "/tmp/bb6-depth4-frontier.tsv"
    ("status\tweight\tdepth\taudit_stop\toracle_outcomes\tprobe_kind\tprobe_steps\tprobe_state\tprobe_head\tprobe_ones\tprobe_next_slot\tpath\n" ++
      String.intercalate "\n" (terms.map encodeTerminal) ++ "\n")
  IO.FS.writeFile "/tmp/bb6-depth4-frontier-report.txt"
    (toString report.1 ++ "\n" ++ toString report.2 ++ "\n")
  IO.println s!"BB6_DEPTH4_TERMINAL_COUNT={terms.length}"
  IO.println s!"BB6_DEPTH4_CERTIFIED_LEAVES={certifiedCount}"
  IO.println s!"BB6_DEPTH4_OPEN_LEAVES={openCount}"
  IO.println s!"BB6_DEPTH4_CERTIFIED_MASS={report.1}"
  IO.println s!"BB6_DEPTH4_OPEN_MASS={report.2}"
  IO.println s!"BB6_DEPTH4_TOTAL_MASS={report.1 + report.2}"

#print axioms depth4ResidualManifest_unique
#print axioms depth4ResidualManifest_certifiedMass
#print axioms depth4ResidualManifest_openMass
#print axioms depth4ResidualManifest_totalMass
#print axioms depth4ResidualManifest_exhaustive
#print axioms physicalScanProbe_unknown_matches
#print axioms physicalScanProbe_unknown_exact
#print axioms physicalScanProbe_halt_exact
#print axioms physicalScanProbe_limit_exact
#print axioms physicalScanProbe_halt_exact_for_completion
#print axioms physicalScanProbe_halt_cover
#print axioms physicalScanProbe_unknown_is_raw_prefix
#print axioms physicalScanProbe_limit_is_raw_prefix

end BB6Coverage
