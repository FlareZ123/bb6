import TwoSidedAutomata

namespace BB6.Agent44TwoSidedRows
open BB6.Agent4Automata

/-- Row-wise composition of the original TwoSidedAutomata checker.
    This changes only proof granularity: every premise is exactly one conjunct
    already required by `BB6.Agent4Automata.check`. -/
theorem check_of_rows {p c}
    (hls : 0 < c.left.edges.size)
    (hrs : 0 < c.right.edges.size)
    (hl : (c.left.pop 0).contains (false,0) = true)
    (hr : (c.right.pop 0).contains (false,0) = true)
    (hs : stateOK c 0 false 0 0 = true)
    (hc : ∀ q a, (row c q a).all
      (fun i => stateStepOK p c q a
        (i/c.right.edges.size) (i%c.right.edges.size)) = true) :
    check p c = true := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨hls,hrs⟩,hl⟩,hr⟩,hs⟩,fun q _ a _ => hc q a⟩

#print axioms check_of_rows
end BB6.Agent44TwoSidedRows
