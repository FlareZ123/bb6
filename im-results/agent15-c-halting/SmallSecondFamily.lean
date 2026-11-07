import CLine
import CFeederCertificate

namespace BB6.Agent15

private def S17 : List (Nat × Nat × Nat) :=
  [(0,2,14), (1,1,15), (2,0,16), (3,4,3), (3,6,1), (3,7,0),
    (4,3,4), (5,2,5), (6,1,6), (7,0,7)]

private theorem S17_rank : BB6Agent6.C.rankCheck 18 S17 = true := by decide
private theorem S17_closed : BB6Agent6.C.boundedCheck 18 S17 = true := by decide
private theorem S17_initial : (5,0,1) ∉ S17 := by decide
private theorem S17_contains_target : (3,7,0) ∈ S17 := by decide

/-- Agent 6's finite backward-closed certificate also excludes the
intermediate c=0 state (3,7,0), not only its downstream feeder (0,2,14). -/
theorem blank_run_ne_3_7 (n : Nat) :
    BB6Agent6.C.run n (5,0,1) ≠ some (3,7,0) :=
  BB6Agent6.C.blank_excluded_by_certificate 18 S17 S17_closed S17_rank
    S17_initial n (3,7,0) S17_contains_target

/-- Translate the original-source CLine reach relation into the independently
copied Agent 6 deterministic run. The transition functions are definitionally
identical. -/
theorem line_reach_to_agent6_run {s : Nat × Nat × Nat}
    (h : BB6CLine.Reach s) :
    ∃ n, BB6Agent6.C.run n (5,0,1) = some s := by
  induction h with
  | init =>
      exact ⟨0, rfl⟩
  | next s t hs hstep ih =>
      rcases ih with ⟨n, hn⟩
      have hnext : BB6Agent6.C.next s = some t := by
        simpa [BB6Agent6.C.next, BB6CLine.nextC] using hstep
      refine ⟨n+1, ?_⟩
      simp [BB6Agent6.C.run, hn, hnext]

/-- The sole small second-family point (j,m)=(0,0) is unreachable. -/
theorem source_no_3_7 : ¬ BB6CLine.Reach (3,7,0) := by
  intro h
  rcases line_reach_to_agent6_run h with ⟨n, hn⟩
  exact blank_run_ne_3_7 n hn

#print axioms source_no_3_7

end BB6.Agent15
