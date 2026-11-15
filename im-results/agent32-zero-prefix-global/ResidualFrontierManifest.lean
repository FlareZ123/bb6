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

/-- The probe's unknown-input case is exactly the slot selected by the
    original firstUnknownPhysical branch policy. -/
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
          simp [physicalScanProbe, hp] at h
          cases h
          simp [firstUnknownPhysical, hp]
      | some t =>
          cases t with
          | none =>
              simp [physicalScanProbe, hp] at h
          | some mv =>
              have hnext :
                  physicalScanProbe p n (successfulMoves+1)
                    (finiteMove cfg mv) = .unknown k d slot := by
                simpa [physicalScanProbe, hp] using h
              have hscan := ih (successfulMoves+1) (finiteMove cfg mv) k d hnext
              simpa [firstUnknownPhysical, hp] using hscan

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
    else "halt=0,ray=0,zero=0,lasso=0,entryMacro=0"
  let probeFields :=
    if term.certified then ["-", "0", "-", "0", "", "-"]
    else encodeProbeFields (physicalScanProbe p 12 0 finiteBlank)
  String.intercalate "\\t"
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
  let terms := depth4ResidualTerminals
  let report := depth4ResidualAudit.report
  let openCount := (terms.filter (fun t => !t.certified)).length
  let certifiedCount := (terms.filter (fun t => t.certified)).length
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

end BB6Coverage
