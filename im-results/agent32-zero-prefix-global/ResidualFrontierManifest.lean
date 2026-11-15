import LassoTraceAudit
import FrontierUnique
import FrontierManifestMass
import Symmetry

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

def encodeEntry (entry : Slot × Transition) : String :=
  toString entry.1.1.val ++ encodeBit entry.1.2 ++ ":" ++ encodeTransition entry.2

def encodeTerminal (term : AuditTerminal) : String :=
  (if term.certified then "C" else "O") ++ "\t" ++ toString term.weight ++ "\t" ++
    String.intercalate "," (term.path.map encodeEntry)

def encodeManifest (terms : List AuditTerminal) : String :=
  "status\tweight\tpath\n" ++
    String.intercalate "\n" (terms.map encodeTerminal) ++ "\n"

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
  IO.FS.writeFile "/tmp/bb6-depth4-frontier.tsv" (encodeManifest terms)
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

end BB6Coverage
