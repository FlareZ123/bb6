# Raw139 F/1 = 0LF: a complete candidate three-hole closure

**Status:** The complete proof source is preserved. All thirteen infinite-run recurrences were kernel-checked locally on Lean 4.36.0-rc2 against the copied zipper semantics; the original-source weighted-cover check has not yet passed. Do not remove this residual from an accepted frontier until the pinned source audit passes.

The exact parent table, in order A0,A1,...,F1, is `[7,24,11,24,14,21,3,16,12,11,24,20]` (code = 4*destination + 2*write + right, 24 = unassigned). Its F1 action is 0LF, distinct from the previously closed 0RF, 0RD and 1LF siblings. The candidate theorem is `BB6.Agent41F1ZeroLF.all_completions_weighted : ∀ m, compatible parent m → WeightedBound 1603 m`.

The 12 internal first-hole splits generate 277 terminal leaves: 147 translated cycles, 72 last-hole queries, 45 FAR certificates, and 13 infinite growth proofs. The longest remaining last-hole query is at 1597 moves, leaving the standard six-step weighted allowance. The certificate uses the existing `FastThreeHoleAudit` with exact literal table matching.

## New unbounded mechanisms

A symbolic zipper interpreter (`Agent41SymSweep.lean`) treats arbitrary finite tape segments as opaque gap variables. It refuses a computation that attempts to read a gap. Its soundness theorem `run_sound` transports each successful finite symbolic trace to every assignment of those segments. This gives checked sweep premises for arbitrary repetitions, not extrapolation from a sampled sequence.

Twelve exceptional cylinders admit exact affine-cost recurrence families. For H9 the suffix is instead a recursively nested carry counter:

- Counter constructors low, high, a(g), b(g), c(g), d(g).
- Next sends low→high→a(low), a(g)→b(g)→c(g)→d(g)→a(next(g)).
- The tape tail words are 011, 0111111, 000111·0·tail(g), 011111·0·tail(g), 0001111·tail(g), 0111111·tail(g), respectively.
- The core starts in C with left word 1·L, right tail(g), and reaches D with left L and right 0·tail(next(g)). Its exact costs are 37,33,9,25,9,24+coreCost(g), proved by structural induction.
- The outer D stage has left word 1 and right word 1111·(11)^n·110·tail(g); after 20n+93+coreCost(g) moves it reaches the stage (n+2,next(g)).
- The actual blank entry reaches stage(0,low) after 68 moves. Thus every compatible completion runs forever.

## Reproduction

The four original-source Lean modules are contained in [Agent41F1ZeroLFProofs.tar.xz.b64](Agent41F1ZeroLFProofs.tar.xz.b64), archive SHA-256 `15b951ad6c8c9b988e2a2f44a39671a938b4c2b0fbc264c72a4afe1a972b62bb`. Run `bash im-results/agent41-raw139-f1-zeroLF/reproduce.sh` at the repository root with Lean 4.36.0-rc2. The manual workflow `agent41-raw139-f1-zeroLF.yml` pins the source SHA and audits the theorem axiom sets. The remaining global obligation is to integrate this exact literal parent into the raw139 residual frontier at champion score, then close all other retained representatives. No BB(6) exactness claim follows from this sibling alone.
