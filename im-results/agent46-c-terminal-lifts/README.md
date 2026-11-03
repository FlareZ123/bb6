# Machine C terminal inverse lift and new high-stop subfamily (Agent 46)

**Status 2026-11-03:** Local Lean 4.36.0-rc2 proof compilation passed against exact original `BB6CLine.nextC` definitions and a *signature-compatible local mock* for the two previously source-certified backward cores. **The complete source proof is pending direct GitHub Actions verification.** No BB(6) exact value or Machine C nonhalting theorem is claimed.

## Mechanism

For any accelerated Machine C state `(a,K,0)` with `K≥4`, the entire genuine blank-start predecessor chain is forced for its last two transitions:
```
(a,K-3,3) -> (a,K-1,1) -> (a,K,0).
```
Proof: the only transition into a c=0 state is from c=1. For target c=1 and K-1≥3, the alternative c=0 resets and c=4 even-middle transition have smaller middle counters, leaving precisely c=3. The Lean source proves both uniqueness statements by complete `nextC` case analysis, and backward transports genuine `BB6CLine.Reach`.

Applying the already established universal backward-closed `A4Backward.bad` and `A4BackwardB.badB` to the forced c=3 ancestor yields four entire terminal-cylinder exclusions for genuine blank-accelerated reachability:

| `a % 48` | `K % 24` | core |
|---:|---:|---|
| 3 | 7 | A |
| 27 | 19 | A |
| 11 | 11 | B |
| 35 | 23 | B |

Each is quantified over all naturals and K≥4. The source also includes four Lean theorems `no_reach_*`, without a quotient BFS.

## Halting-gate intersection

The source-verified Agent15 immediate high-stopping criterion is `a=2*j+3` and `K+j+3*m+5=2^(2*m+2)*(j+3)`. For **all** `j%12=0` and `m%8=4`, the stopping equation forces `K≥4`, `(2*j+3)%48=3 or 27`, and respectively `K%24=7 or 19`. The theorem `high_stop_j12_m4_excluded` rules out every such genuine blank-accelerated stopping target. The proof derives `2^(2*m+2)%24=16` by all-depth induction and uses the exact source core A invariant; no finite cutoff or sampled trend is involved.

This excludes 16 residue pairs `(j mod 48,m mod 8)` if count is expressed as a Cartesian lattice with j∈{0,12,24,36} and m=4; equivalently 2 distinct `j mod24` classes and one `m mod8` class. **The 16-pair phrasing is deliberately not used as an exact count until independently reviewed**. [Note: a pair count at `mod48×mod8` is four, not sixteen; the mathematically invariant parameter description is authoritative.]

The result appears disjoint from Agent4's four singleton high-gate parameter families `j%48∈{5,13,29,37}` and Agent3's newly certified `m%4=2` high-family. It must still be checked against all earlier source-certified quotients, inverse normalizers, and external literature before asserting originality.

## Reproduction and verification boundary

The immutable source chain is Agent11 `CLine.lean`, Agent4 `BackwardMod.lean`, `SourceBridge.lean`, `BackwardModB.lean`, `SourceBridgeB.lean`. The manual-only workflow `.github/workflows/agent46-c-terminal-lifts.yml` recompiles those unchanged files first, then `Agent46TerminalLifts.lean` with `#print axioms` on the final claims. Local proof development used a lightweight mock with `source_blank_never_bad` and `source_blank_never_badB` declared as axioms; this is only a syntax/type test and **must never be cited as original-source certification**.

No general Machine C blank nonhalting, complete two-family exclusion, raw BB(6) solution, or universal upper bound follows. This stays in `im-results/`. Next: inspect full source CI, check source axioms and novelty, then test whether another forced inverse level excludes remaining high and first-stopping sectors.
