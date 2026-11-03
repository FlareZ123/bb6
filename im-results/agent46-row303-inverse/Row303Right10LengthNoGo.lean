import Row303GateOriginal

namespace BusyBeaver.M_1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LFHHH_1LD1LF

private def sectionRun : Nat → Option State → Option State
  | 0, s => s
  | n+1, s => (sectionRun n s).bind next

/-- The original blank accelerator reaches this exact section after 33
    successful source returns, verified by kernel evaluation. -/
private theorem section_run_33 :
    sectionRun 33 (some (.E [1] [])) =
      some (.E [] [1,3,0,1,2,0,1,2,0,1,0,2,0,1]) := by
  decide

private theorem s0 : next (.E [] [1,3,0,1,2,0,1,2,0,1,3,2,0,0]) =
    some (.E [2,2,1,1,1,1,1,1,1,1,2,1,1,1,1] []) := rfl
private theorem s1 : next (.E [2,2,1,1,1,1,1,1,1,1,2,1,1,1,1] []) =
    some (.E [4,1,1,1,1,1,1,1,1,2,1,1,1,1] []) := rfl
private theorem s2 : next (.E [4,1,1,1,1,1,1,1,1,2,1,1,1,1] []) =
    some (.E [1,1,1,0,1,1,1,1,1,1,1,1,2,1,1,1,1] []) := rfl
private theorem s3 : next (.E [1,1,1,0,1,1,1,1,1,1,1,1,2,1,1,1,1] []) =
    some (.E [3,0,1,1,1,1,1,1,1,1,2,1,1,1,1] [1]) := rfl

/-- Inductive lift from one-step all-context closure to genuine rooted
    acceleration histories. -/
private theorem propagate (P : List Nat → List Nat → Nat → Prop)
    (hstart : P [1] [] 0)
    (hclose : ∀ L R L' R', P L (R.take 10) R.length →
      next (.E L R) = some (.E L' R') → P L' (R'.take 10) R'.length) :
    ∀ n L R, sectionRun n (some (.E [1] [])) = some (.E L R) →
        P L (R.take 10) R.length := by
  intro n
  induction n with
  | zero =>
      intro L R h
      have hp : (State.E L R) = State.E [1] [] := by
        simpa only [sectionRun, Option.some.injEq] using h.symm
      cases State.E.inj hp with
      | intro hl hr =>
        cases hl; cases hr; exact hstart
  | succ n ih =>
      intro L R h
      cases hp : sectionRun n (some (.E [1] [])) with
      | none => simp [sectionRun, hp] at h
      | some p =>
        cases p with
        | E l r =>
          have ht : next (.E l r) = some (.E L R) := by
            simpa only [sectionRun, hp, Option.bind_some] using h
          exact hclose l r L R (ih l r hp) ht

/-- A complete left stack, the first 10 right zero-run entries, and right-stack length
    cannot support a context-universal, inductive halting exclusion.
    The actual rooted run is followed through section 33, then its
    unobserved right suffix is replaced by a different suffix of equal length. -/
theorem right_prefix_ten_length_closure_forces_precursor
    (P : List Nat → List Nat → Nat → Prop)
    (hstart : P [1] [] 0)
    (hclose : ∀ L R L' R', P L (R.take 10) R.length →
      next (.E L R) = some (.E L' R') → P L' (R'.take 10) R'.length) :
    P [3,0,1,1,1,1,1,1,1,1,2,1,1,1,1] [1] 1 := by
  have h33 := propagate P hstart hclose 33 []
    [1,3,0,1,2,0,1,2,0,1,0,2,0,1] section_run_33
  have hsynthetic : P [] ([1,3,0,1,2,0,1,2,0,1,3,2,0,0].take 10) 14 := h33
  have h34 := hclose [] [1,3,0,1,2,0,1,2,0,1,3,2,0,0]
    [2,2,1,1,1,1,1,1,1,1,2,1,1,1,1] [] hsynthetic s0
  have h35 := hclose [2,2,1,1,1,1,1,1,1,1,2,1,1,1,1] []
    [4,1,1,1,1,1,1,1,1,2,1,1,1,1] [] h34 s1
  have h36 := hclose [4,1,1,1,1,1,1,1,1,2,1,1,1,1] []
    [1,1,1,0,1,1,1,1,1,1,1,1,2,1,1,1,1] [] h35 s2
  exact hclose [1,1,1,0,1,1,1,1,1,1,1,1,2,1,1,1,1] []
    [3,0,1,1,1,1,1,1,1,1,2,1,1,1,1] [1] h36 s3

theorem no_right_prefix_ten_length_inductive_halting_shield
    (P : List Nat → List Nat → Nat → Prop)
    (hstart : P [1] [] 0)
    (hclose : ∀ L R L' R', P L (R.take 10) R.length →
      next (.E L R) = some (.E L' R') → P L' (R'.take 10) R'.length)
    (hsafe : ∀ L RP N, P L RP N → ¬preGate L) : False := by
  have hp := right_prefix_ten_length_closure_forces_precursor P hstart hclose
  have hc : preGate [3,0,1,1,1,1,1,1,1,1,2,1,1,1,1] := by trivial
  exact hsafe [3,0,1,1,1,1,1,1,1,1,2,1,1,1,1] [1] 1 hp hc

#print axioms right_prefix_ten_length_closure_forces_precursor
#print axioms no_right_prefix_ten_length_inductive_halting_shield
end BusyBeaver.M_1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LFHHH_1LD1LF
