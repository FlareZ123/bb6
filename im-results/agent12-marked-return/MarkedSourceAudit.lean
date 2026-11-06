import IncrementalAudit
import MarkedHaltBranch

namespace BB6Coverage

/-- These are exact original-source genuine read-one cylinders:
    80 all-symbol nonhalt traps and 20 exact score-three halters. -/
def markedSourceCases : List PartialMachine :=
  markedSinkCases ++ markedHaltCases

theorem markedSourceCases_length : markedSourceCases.length = 100 := by decide

/-- Every inserted cylinder has an actual source-verified proof for
    every fully specified completion, for bound 3. -/
theorem markedSourceCover (p : PartialMachine)
    (h : p ∈ markedSourceCases) : Cover (DecidedBelow 3) p := by
  rcases List.mem_append.mp h with hs | hh
  · rcases List.mem_map.mp hs with ⟨t, ht, hp⟩
    rcases t with ⟨q, dir, w0, w1, e⟩
    subst p
    exact markedSink_source_cover q dir w0 w1 e 3 ht
  · rcases List.mem_map.mp hh with ⟨t, ht, hp⟩
    rcases t with ⟨q, dir, w0⟩
    subst p
    exact markedHalt_source_cover q dir w0 ht

/-- Source-backed globally exhaustive *partial* proof tree. This
    construction actually inserts the certificates into an initial
    globally open six-state 25-way frontier. Any other full machine
    remains unresolved. -/
noncomputable def markedSourceGlobalAudit :
    FrontierAudit (DecidedBelow 3) emptyTable :=
  markedSourceCases.attach.foldl
    (fun acc x => addCertificate acc x.1 (markedSourceCover x.1 x.2))
    (.unresolved emptyTable)

theorem markedSourceGlobal_exhaustive (m : Machine) :
    DecidedBelow 3 m ∨ markedSourceGlobalAudit.open m :=
  markedSourceGlobalAudit.exhaustive m (empty_compatible m)

theorem markedSourceGlobal_conserves :
    markedSourceGlobalAudit.report.1 +
      markedSourceGlobalAudit.report.2 = 25^12 := by
  calc
    _ = cylinderMass emptyTable := markedSourceGlobalAudit.report_conserves
    _ = 25^12 := by decide

#print axioms markedSourceCases_length
#print axioms markedSourceCover
#print axioms markedSourceGlobal_exhaustive
#print axioms markedSourceGlobal_conserves

end BB6Coverage
