# Agent 31: source-accepted 76-residual two-parent reduction

Timestamp: 2026-11-25T20:48:33.067Z.

The concrete raw107+raw114 two-parent wrapper is now source-accepted. In workflow run [45647053824](https://github.com/FlareZ123/bb6/actions/runs/45647053824), exactness job 139320746934 succeeded: it compiled `Raw107ParentClosure` and `CanonicalTwoParentRosterOnly.exact_at_target`, reused 51 accepted core modules, preserved the accepted Raw114 object hash, and checked theorem axiom profiles containing only `propext`, `Classical.choice`, and `Quot.sound`.

The proved dichotomy is:
`∀ m, compatible root m → WeightedBound 7014 m ∨ ∃ e ∈ roster76, TNFQuotientCompatible e.2 m`,
with `roster76.length = 76`. For any `B ≥ 7014`, `exact_at_target` reduces exact BB(6) to Covers for those 76 retained representatives plus the explicit attaining champion witness. This is a conditional maximality reduction, **not** an upper bound or exact BB(6) value.

Important artifact-label trap: artifact 15043876968 is named `canonical73-raw110-raw112-roster-consumer-certified`, but its embedded manifest reports residual_count 76 and theorem `BB6.Agent31CanonicalTwoParentRosterOnly.exact_at_target`. The overall run failed only in a separate downstream canonical72 job; the exactness job succeeded and uploaded the artifact. The reusable Raw107 core artifact is 15043282896.

I promoted the result into `results/2026-11-25-canonical76-two-parent-reduction-agent31.md` and updated `results/README.md`. Do not report 73 or 72 as accepted yet. The follow-on canonical73/72 source audit is run [45697687963](https://github.com/FlareZ123/bb6/actions/runs/45697687963), currently in progress; it attempts additional Raw117/Raw112/Raw110/Raw121 composition.
