import Row303GateOriginal

namespace BusyBeaver.M_1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LFHHH_1LD1LF

private theorem e1 : next (.E [1] []) = some (.E [1,1] []) := rfl
private theorem e2 : next (.E [1,1] []) = some (.E [] [1]) := rfl
private theorem e3 : next (.E [] [3,2]) = some (.E [2,2,1,1,1] []) := rfl
private theorem e4 : next (.E [2,2,1,1,1] []) = some (.E [4,1,1,1] []) := rfl
private theorem e5 : next (.E [4,1,1,1] []) = some (.E [1,1,1,0,1,1,1] []) := rfl
private theorem e6 : next (.E [1,1,1,0,1,1,1] []) = some (.E [3,0,1,1,1] [1]) := rfl

/-- Any purely left-stack predicate containing the genuine blank left seed [1]
    and closed for every right-stack context must contain a terminal precursor.
    Intermediate right contexts are intentionally independently chosen.
    The theorem does not assert a genuine blank-orbit visit. -/
theorem left_only_closure_forces_precursor (P : List Nat → Prop)
    (hstart : P [1])
    (hclose : ∀ (L R L' R' : List Nat), P L →
      next (.E L R) = some (.E L' R') → P L') :
    P [3,0,1,1,1] := by
  have h1 := hclose [1] [] [1,1] [] hstart e1
  have h2 := hclose [1,1] [] [] [1] h1 e2
  have h3 := hclose [] [3,2] [2,2,1,1,1] [] h2 e3
  have h4 := hclose [2,2,1,1,1] [] [4,1,1,1] [] h3 e4
  have h5 := hclose [4,1,1,1] [] [1,1,1,0,1,1,1] [] h4 e5
  exact hclose [1,1,1,0,1,1,1] [] [3,0,1,1,1] [1] h5 e6

/-- No all-right-context left-only inductive shield containing the genuine
    left seed can exclude every first-return halting precursor. -/
theorem no_left_only_inductive_halting_shield (P : List Nat → Prop)
    (hstart : P [1])
    (hclose : ∀ (L R L' R' : List Nat), P L →
      next (.E L R) = some (.E L' R') → P L')
    (hsafe : ∀ L, P L → ¬preGate L) : False := by
  have hp := left_only_closure_forces_precursor P hstart hclose
  have hc : preGate [3,0,1,1,1] := by trivial
  exact hsafe [3,0,1,1,1] hp hc

#print axioms left_only_closure_forces_precursor
#print axioms no_left_only_inductive_halting_shield
end BusyBeaver.M_1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LFHHH_1LD1LF
