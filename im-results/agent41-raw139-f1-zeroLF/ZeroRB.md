# Raw139 F/1 = 0RB — source-certified exhaustive closure

**Status: SOURCE-ACCEPTED.** The complete original-source Lean 4.36.0-rc2 dependency closure passed in [run 45609382340](https://github.com/FlareZ123/bb6/actions/runs/45609382340), pinned to commit `464020270a1d82800bcebb7071831e58ac911bc7`. The workflow exported manifest and compiled objects as artifact `15018818460` (`raw139-f1-zeroRB-certified`). Its reproduction script audits the final theorem, the symbolic interpreter, the checked wrapper, both non-affine mechanisms, and all 23 nonhalting theorems against the allowlist `propext`, `Classical.choice`, `Quot.sound`; the script fails if an audit is missing or any other axiom (including `sorryAx` or `native_decide`) appears.

The exact parent table, in order A0,A1,...,F1, is `[7,24,11,24,14,21,3,16,12,11,24,5]` (code = 4*destination + 2*write + right, 24 = unassigned). The certified theorem is `BB6.Agent41F1ZeroRB.all_completions_weighted : ∀ m, compatible parent m → WeightedBound 290 m`. The original-source acceptance is independent of, and does not yet establish, integration into the global raw139 residual frontier.

Partition: 20 internal splits; 461 terminal leaves = 194 translated cycles + 164 last-hole queries + 80 FAR + 23 growth proofs. Maximum last-hole query 241; bound 290 is conservative.

## Two non-affine growth mechanisms

- H19: after 55 blank-start steps, stage `param 0` (state A, left `01`, right `011111 · (111)^n · 001111`). Entry costs 15n+32 and initializes unary drain with a=6+3n, b=0. Inner word `01 · 1^a · 00 · 1^(6+b)` in state C. Each decrement a+1→a adds 3 to b and costs 4a+12, verified symbolically for arbitrary suffix. Induction drains to a=0, b=3(6+3n). Exit costs 3b+50 and yields stage `param (3n+7)`. All costs positive; exact recurrence gives nonhalting for every completion.
- H20: stage reached after 55 steps, with `011111 · (111111111)^n · 001111` on the right. Entry costs 9n+51. The inner fixed-length little-endian word begins `[false,true,false]` followed by 3n zeros; encode true as 111 and false as 100. A binary increment with k trailing low-order ones costs 12k+30 and never reads beyond the arbitrary suffix. The rank `zeroRank`, which interprets the bitwise complement as a little-endian natural, decreases by exactly one at each increment; length is preserved. Well-founded induction proves a finite run to the all-ones word, without a fuel cutoff. Exit then produces stage n+1. This proves genuine nonhalting despite exponentially long inner loops.
- The other 21 exceptional leaves have affine or phase/block recurrences.

## Reproduction

Run `bash im-results/agent41-raw139-f1-zeroLF/reproduce-zeroRB.sh`. The archive SHA-256 is `dedb53f31b5493b240d1b1d89fa1c409f0ced92ef1d6486c5415e6d98fe75aba`. The script reuses only `Agent41SymSweep.lean` from the source-accepted 0LF archive, reconstructs the exact generated source, compiles the original-source dependency closure, writes a manifest and compiled objects, and checks every named theorem's transitive axiom profile. The global roster consumer and its exact complement remain separate proof obligations.
