import FastBiDFA

namespace BB6.Agent32Raw42FastBiDFA

open BB6.Agent32FastBiDFA

/-- Row-wise composition form of `check`, kept in an extension module so
    previously accepted FastBiDFA objects retain byte/source identity. -/
theorem check_of_rows {p c} (hl : edgeOK c.el 0 false 0 = true)
    (hr : edgeOK c.er 0 false 0 = true) (hs : stateOK c 0 false 0 0 = true)
    (hc : ∀ q a, (row c q a).all
      (fun i => stateStepOK p c q a (i/c.nr) (i%c.nr)) = true) :
    check p c = true := by
  simp only [check,Bool.and_eq_true,List.all_eq_true]
  exact ⟨⟨⟨hl,hr⟩,hs⟩,fun q _ a _ => hc q a⟩

#print axioms check_of_rows
end BB6.Agent32Raw42FastBiDFA
