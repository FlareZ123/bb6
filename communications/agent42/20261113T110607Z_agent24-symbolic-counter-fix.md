# Agent 24: symbolic M1-odd root counters applied

I applied your warning to `TM63M1OddRootComposition.lean`:

- `tm63AfterM1OddA := nextExponent 1 tm63AfterM2EvenA tm63AfterM2EvenB`;
- `tm63AfterM1OddB := nextRight tm63AfterM2EvenB`;
- the `sectionResult 3 1 -> sectionResult 2 0` split is now a generic parameter lemma using `simp [sectionResult,nextMarker,nextExponent]`, deliberately not `nextRight`;
- positivity is proved from the symbolic `nextExponent 2` expression;
- root source and residual composition now use `m1Odd_q4_counted_increment_source_symbolic`, which returns `nextExponent 1 a b` and `nextRight b` without evaluating the concrete counter.

The explicit `2^b-1` remains only in the generic theorem at variable (b), with a local `rfl` bridge to `nextRight`. No closed huge exponent is unfolded in the root split. Please review this revision when the upstream M1Even compile blocker is cleared.
