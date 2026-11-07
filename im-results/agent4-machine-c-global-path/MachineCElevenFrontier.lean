import MachineCFrontier

namespace BB6Coverage

set_option maxRecDepth 12000
set_option maxHeartbeats 0

private theorem open_lasso_step_24 (p : PartialMachine) (d : Nat)
    (slot : Slot)
    (hf : lassoDecisionOracle p 6 6 12 2 4 = false)
    (hs : firstUnknownPhysical p 24 finiteBlank = some slot) :
    (lassoPhysicalTraceAudit p 6 6 24 12 2 4 (d+1)).open machineC ↔
      (lassoPhysicalTraceAudit
        (refine p slot (machineC slot)) 6 6 24 12 2 4 d).open machineC := by
  have hn : ¬ lassoDecisionOracle p 6 6 12 2 4 = true := by simp [hf]
  rw [lassoPhysicalTraceAudit.eq_2]
  split
  · rename_i hhit
    exact False.elim (hn hhit)
  · split
    · rename_i hnone
      cases hnone.symm.trans hs
    · rename_i found hfound
      have heq : found = slot := by simpa [hfound] using hs
      subst found
      rfl

/-- Eleven actual table-input consultations, including the read-one rows.
    The finite quantifier is explicit: no inferred zero-read control path. -/
theorem machineC_eleven_first_unknown (n : Nat) (hn : n < 11) :
    firstUnknownPhysical (machineCPrefix n) 24 finiteBlank =
      some (machineCVisited[n]!) := by
  have hall : ∀ i : Fin 11,
      firstUnknownPhysical (machineCPrefix i.val) 24 finiteBlank =
      some (machineCVisited[i.val]!) := by decide
  exact hall ⟨n, hn⟩

/-- The true next physical scanner choice exactly extends the sparse
    Machine C table by one original instruction, at each of 11 stages. -/
theorem machineC_eleven_prefix_ext (n : Nat) (hn : n < 11) :
    refine (machineCPrefix n) (machineCVisited[n]!)
      (machineC (machineCVisited[n]!)) = machineCPrefix (n+1) := by
  funext s
  have hall : ∀ i : Fin 11, ∀ s : Slot,
      refine (machineCPrefix i.val) (machineCVisited[i.val]!)
        (machineC (machineCVisited[i.val]!)) s =
          machineCPrefix (i.val+1) s := by decide
  exact hall ⟨n, hn⟩ s

/-- None of the already source-sound finite halt, fresh-ray, lasso, or
    finite-entry-macro tests prove a verdict at any one of the twelve
    sparse stages along the authentic Machine C route. -/
theorem machineC_eleven_oracles_decline (n : Nat) (hn : n ≤ 11) :
    lassoDecisionOracle (machineCPrefix n) 6 6 12 2 4 = false := by
  have hall : ∀ i : Fin 12,
      lassoDecisionOracle (machineCPrefix i.val) 6 6 12 2 4 = false := by
    decide
  exact hall ⟨n, by omega⟩

/-- Structural induction on the number of remaining genuine branch
    decisions. The witness is a single path in the original global
    source-sound audit; it does not require evaluating the full 25-way
    tree or accepting a computationally guessed nonhalting claim. -/
private theorem eleven_path_open (depth : Nat) :
    ∀ n : Nat, n + depth = 11 →
      (lassoPhysicalTraceAudit
        (machineCPrefix n) 6 6 24 12 2 4 depth).open machineC := by
  induction depth with
  | zero =>
      intro n hn
      have he : n = 11 := by omega
      subst n
      have hf : lassoDecisionOracle (machineCPrefix 11) 6 6 12 2 4 = false :=
        machineC_eleven_oracles_decline 11 (by decide)
      simp [lassoPhysicalTraceAudit, FrontierAudit.open, hf]
  | succ depth ih =>
      intro n hsum
      have hn : n < 11 := by omega
      let slot : Slot := machineCVisited[n]!
      have hf : lassoDecisionOracle (machineCPrefix n) 6 6 12 2 4 = false :=
        machineC_eleven_oracles_decline n (by omega)
      have hs : firstUnknownPhysical (machineCPrefix n) 24 finiteBlank =
          some slot := machineC_eleven_first_unknown n hn
      have hext : refine (machineCPrefix n) slot (machineC slot) =
          machineCPrefix (n+1) := machineC_eleven_prefix_ext n hn
      have htail : (lassoPhysicalTraceAudit
          (machineCPrefix (n+1)) 6 6 24 12 2 4 depth).open machineC :=
        ih (n+1) (by omega)
      exact (open_lasso_step_24 (machineCPrefix n) depth slot hf hs).mpr
        (by simpa only [hext] using htail)

/-- The authentic Machine C root lies in a specific original-branch open
    cylinder in the **eleven-level** all-six-state source-sound global
    lasso/macro audit, with every other source row free as required. -/
theorem machineC_depth_eleven_open :
    (lassoPhysicalTraceAudit emptyTable 6 6 24 12 2 4 11).open
      machineC := by
  have h := eleven_path_open 11 0 (by decide)
  simpa [machineCPrefix] using h

/-- The still-open cylinder reached by eleven authentic source splits has
    only the F/0 transition unassigned and exact cylinder mass 25. -/
theorem machineC_depth_eleven_leaf_mass :
    cylinderMass (machineCPrefix 11) = 25 := machineCPrefix_mass

#print axioms machineC_eleven_first_unknown
#print axioms machineC_eleven_prefix_ext
#print axioms machineC_eleven_oracles_decline
#print axioms machineC_depth_eleven_open

end BB6Coverage
