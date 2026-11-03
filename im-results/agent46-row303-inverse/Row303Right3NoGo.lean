import Row303GateOriginal

namespace BusyBeaver.M_1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LFHHH_1LD1LF

/-- Steps 0..6 follow the true blank stack orbit. Step 7 changes only the
    fourth right-run entry, keeping the first three right entries unchanged.
    Each edge is literal finite computation under the pinned exact source. -/
private theorem a0 : next (.E [1] []) = some (.E [1,1] []) := rfl
private theorem a1 : next (.E [1,1] []) = some (.E [] [1]) := rfl
private theorem a2 : next (.E [] [1]) = some (.E [1,1,1,1] []) := rfl
private theorem a3 : next (.E [1,1,1,1] []) = some (.E [3,1] [1]) := rfl
private theorem a4 : next (.E [3,1] [1]) = some (.E [1] [2,0,1]) := rfl
private theorem a5 : next (.E [1] [2,0,1]) = some (.E [1,1] [3,0,1]) := rfl
private theorem a6 : next (.E [1,1] [3,0,1]) = some (.E [] [1,3,0,1]) := rfl
private theorem a7 : next (.E [] [1,3,0,3,2]) =
    some (.E [2,2,1,2,1,1,1,1] []) := rfl
private theorem a8 : next (.E [2,2,1,2,1,1,1,1] []) =
    some (.E [4,1,2,1,1,1,1] []) := rfl
private theorem a9 : next (.E [4,1,2,1,1,1,1] []) =
    some (.E [1,1,1,0,1,2,1,1,1,1] []) := rfl
private theorem a10 : next (.E [1,1,1,0,1,2,1,1,1,1] []) =
    some (.E [3,0,1,2,1,1,1,1] [1]) := rfl

/-- Even with the entire left stack and the first three right zero-run entries,
    every all-right-context, return-closed predicate containing the exact blank
    root must admit a one-step halting precursor. The synthetic context change
    at step 7 means this does not prove an actual blank-root halt. -/
theorem right_prefix_three_closure_forces_precursor
    (P : List Nat → List Nat → Prop)
    (hstart : P [1] [])
    (hclose : ∀ L R L' R', P L (R.take 3) →
      next (.E L R) = some (.E L' R') → P L' (R'.take 3)) :
    P [3,0,1,2,1,1,1,1] [1] := by
  have h1 := hclose [1] [] [1,1] [] hstart a0
  have h2 := hclose [1,1] [] [] [1] h1 a1
  have h3 := hclose [] [1] [1,1,1,1] [] h2 a2
  have h4 := hclose [1,1,1,1] [] [3,1] [1] h3 a3
  have h5 := hclose [3,1] [1] [1] [2,0,1] h4 a4
  have h6 := hclose [1] [2,0,1] [1,1] [3,0,1] h5 a5
  have h7 := hclose [1,1] [3,0,1] [] [1,3,0,1] h6 a6
  have hs : P [] ([1,3,0,3,2].take 3) := h7
  have h8 := hclose [] [1,3,0,3,2] [2,2,1,2,1,1,1,1] [] hs a7
  have h9 := hclose [2,2,1,2,1,1,1,1] [] [4,1,2,1,1,1,1] [] h8 a8
  have h10 := hclose [4,1,2,1,1,1,1] [] [1,1,1,0,1,2,1,1,1,1] [] h9 a9
  exact hclose [1,1,1,0,1,2,1,1,1,1] [] [3,0,1,2,1,1,1,1] [1] h10 a10

theorem no_right_prefix_three_inductive_halting_shield
    (P : List Nat → List Nat → Prop)
    (hstart : P [1] [])
    (hclose : ∀ L R L' R', P L (R.take 3) →
      next (.E L R) = some (.E L' R') → P L' (R'.take 3))
    (hsafe : ∀ L RP, P L RP → ¬preGate L) : False := by
  have hp := right_prefix_three_closure_forces_precursor P hstart hclose
  have hc : preGate [3,0,1,2,1,1,1,1] := by trivial
  exact hsafe [3,0,1,2,1,1,1,1] [1] hp hc

#print axioms right_prefix_three_closure_forces_precursor
#print axioms no_right_prefix_three_inductive_halting_shield
end BusyBeaver.M_1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LFHHH_1LD1LF
