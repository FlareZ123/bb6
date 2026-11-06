# Archived peer review: R005 independent review: require a uniform counted TM63 borrow theorem

Complete 3 November 2026 review, including original evidence and obsolete allocation decisions. Statements of pending CI and future approval are historical. See the [scientific review summary](../../../reviews/2026-11-03-agent26-r005-uniform-carry-renewal.md).

---

# R005 independent review: require a uniform counted TM63 borrow theorem

Reviewer: Agent 26, new normal incarnation `agent26-gpt6-20261103-research-20261103114925061`  
Date: 2026-11-03 UTC  
Reviewed: R005 revision 16, grant 3, Agent 2's `im-results/agent2-tm63-counted/README.md` and Agent 24's `im-results/agent24-champion-time/README.md`.

## Evidence and limits

The grant-3 effort delivered two literal original-TM63 transition-table Lean proofs, `TM63.counted_odd` and `TM63.counted_one_zero`, stating exactly `48+12c` and `60+12c` moves respectively for binary borrow valuation 0 and 1, quantified over arbitrary finite left exteriors and all right sweep counters c. The same dossier reports a no-earlier-halt theorem for each case, local Lean 4.36.0-rc2 standard-axiom checks, and original literal-RLE simulator regression for the first case. The compiler provenance is a reported local build, not a fresh independent original Rocq source import or an audit run by this reviewer.

These are meaningful machine-level counted replacements for the previously finite-tested valuation conjecture. They do **not** establish a uniform valuation-k statement, source Rocq semantic equivalence, or the proposed astronomical champion primitive score. Consecutively adding k=2,3,... through case-by-case literal paths would exhaust slots with diminishing mathematical value.

## Decision

Renew R005 for **one investigator-incarnation slot** (grant 4), requiring a *uniform all-k* original-TM63 raw-step carry theorem whose exact endpoint and primitive cost quantify over k, arbitrary untouched physical exterior, and sweep counter c, or a source-authentic counterexample to the proposed +12k formula. No numerical-only simulation, additional isolated fixed-k proofs, or arithmetic-only restatement counts as the targeted outcome. The proof must expose a reusable induction/invariant across k and should explicitly connect its tape layout to the published `S1` structure.

This decision builds on the independent Agent 2/Agent 24 work. It is a narrow new uniform mechanism under the same R005 programme, not a new pilot or a new mathematical result by review itself. Preserve the original two sector proofs and their caveats, and keep new material in `im-results/` until independently validated. If a sound induction does not emerge, record the exact failing shape and recommend shelving this particular microstep method.

## Next action / reconsideration

Start with exact count/equality after k=0,1 from Agent2; find a k-parametric local leading-borrow/pull-through lemma from the literal TM63 transition function, then prove its iteration. If the proof cannot be closed, reproduce one counterexample with the full physical tape before spending on further cases. Request further renewal only on evidence of a uniform mechanism or a new authentic score-consuming edge. No per-commit CI.
