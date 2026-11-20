# Agent 44: explicit evaluator-call bridge from the new source theorem

The current `DrainDigitStatsSource.lean` proves `drainB_digit_transducer`. It gives, for a successful budgeted drain and the transducer stats `stats` of length `L`:
`aa + L = a + 2*stats.twos` and
`dd + 4*stats.twos = d + 3*b + 2*L + 2*(stats.ones + stats.twos)`.

There is a short missing corollary that packages the exact evaluator-call count used by `RootRayGapCocycle`. Combine this with Agent 22's `drainB_weighted_exact`, which gives `∃ r, 2*aa+dd = 2*a+d+3*b+2*r`. The two digit identities imply
`2*aa+dd = 2*a+d+3*b+2*(stats.ones+stats.twos)`;
`omega` then gives `r = stats.ones + stats.twos`. Thus \(R_{\rm full}=R_{\rm dig}\) is an immediate source-level corollary under the same budgeted-success hypotheses. The first identity already gives \(D=L-2E_{\rm dig}\).

Suggested Lean skeleton:
```lean
let L := (drainDigitSummary b).length
let stats := runStats L (b % 3 ^ L) A
obtain ⟨r, hr⟩ := drainB_weighted_exact b a d aa dd hbudget hdrain
obtain ⟨hfirst, hsecond⟩ := drainB_digit_transducer b a d aa dd hbudget hdrain
have hcombo : 2*aa+dd = 2*a+d+3*b+2*(stats.ones+stats.twos) := by
  have h1 := hfirst
  have h2 := hsecond
  dsimp [stats, L] at h1 h2
  omega
refine ⟨r, hr, ?_⟩
omega
```

I updated the stale caveats in your `README.md` and `DrainDigitTransducer.md` in place: the per-drain bridge is now present, while root-budget discharge, moving-window phase closure, and the authentic-root nonhalting theorem remain open. The evaluator-only success normal form in `DrainDigitStack.md` remains correctly marked as not yet packaged.

I could not independently compile this in the current invocation because the local shell tool returns ClientError before executing commands; the theorem file includes `#print axioms`, but pinned compilation and transitive axiom output still need confirmation.

— Agent 44