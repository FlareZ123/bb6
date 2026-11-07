# Even, odd-even, and two-wave B/0 return families

Date: 2026-11-07  
Status: source-import verified in Lean 4.36.0-rc2; finite census corroboration only.

## Result

Let (b=(B,h,t)) be a reached configuration with (t(h)=0) and the three-cell left prefix

[
t(h-1)=1,qquad t(h-2)=0,qquad t(h-3)=1.
]

Let (m) be one plus the length of the consecutive run of ones beginning at (h+1). Two exact first-return laws apply.

### Even prefix family

For (m=2n+2), assume

[
t(h+1+j)=1quad(0le j<2n+1),
]
[
t(h+2n+2)=0,qquad t(h+2n+3)=0.
]

Then the machine returns to a reached (B/0) configuration after

[
T=m+13=2n+15
]

steps, with returned head

[
h'=h+m+1=h+2n+3.
]

The proof is in `b0_even_prefix_to_b0_exact`; the original `b0_even_prefix_to_b0` name remains as a backwards-compatible wrapper. Its exact tail lemma is `evenSweep_to_B_exact`: a D-state traverses an even block of ones, reads the zero sentinel, and executes the three-step D/0, E/0, A/0 return to B/0. The proof retains the exact resulting tape.

### Odd-then-even prefix family

For (m=2n+1), assume

[
t(h+1+j)=1quad(0le j<2n),
]
[
t(h+2n+1)=0,quad t(h+2n+2)=0,quad t(h+2n+3)=0.
]

Then the machine returns to a reached (B/0) configuration after

[
T=3m+20=6n+23
]

steps, with returned head

[
h'=h+m+2=h+2n+3.
]

The proof is in `b0_odd_even_chain_to_b0_exact`; the original `b0_odd_even_chain_to_b0` name remains as a backwards-compatible wrapper. It composes the nine-step prefix, the existing odd F/1 wave theorem, the B/1-to-F/1 transition, and the exact even D-sweep return.

These are conditional local return theorems. They do not classify every reached B/0 configuration and do not establish a global BB(6) upper bound.

## Lean verification

Source files: `Root119OddEvenChain.lean`, `Root119TwoWaveRootPrefix.lean`  
Workflow: `.github/workflows/agent42-root119-even-wave-prefix.yml`  
Successful source-import runs: [42405102264](https://github.com/FlareZ123/bb6/actions/runs/42405102264), [42423330099](https://github.com/FlareZ123/bb6/actions/runs/42423330099), [42423714896](https://github.com/FlareZ123/bb6/actions/runs/42423714896)

The workflow compiles the dependency closure from source and checks the axiom output. The relevant declarations report:

- `evenSweep_to_B_exact`: [propext, Classical.choice, Quot.sound]
- `b0_even_prefix_to_b0`: [propext, Classical.choice, Quot.sound]
- `b0_odd_even_chain_to_b0`: [propext, Classical.choice, Quot.sound]
- `b0_two_wave_prefix`: [propext, Quot.sound]
- `b0_two_wave_root_interval_to_b0` and `b0_two_wave_root_interval_avoids_BBad`: [propext, Classical.choice, Quot.sound]

No relevant declaration depends on `sorryAx`. The local Lean 4.36.0-rc2 model proof for the even-sweep composition also compiled independently before the source-import run.


## NoLeft4 shield transport (7 November 2026)

The new source-import module [Root119PrefixShield.lean](Root119PrefixShield.lean) proves that the even prefix return preserves NoLeft4 true true false under the input shield alone. The odd-even prefix return also preserves it under the input shield plus the explicit local boundary condition

\[
\neg(t(h-6)=1\land t(h-5)=1\land t(h-4)=0).
\]

The proof follows the exact intermediate tape configurations. In the even family, the prefix exposes only cells ending in 1, the F/1 transition writes 0 after a 1, and the even D sweep has no adjacent zero pair in its swept interval. In the odd-even family, the B/1 retreat is a leftward head shift; the next F/1 write at h-3 can expose one new 1100 window, exactly the window h-6 through h-3. The boundary condition excludes it, after which the same even-sweep lemma applies. The condition is sharp: the new theorem b0_odd_even_chain_to_b0_exact_bad_boundary proves that if the forbidden 110 boundary pattern is present, the exact return output contains 1100 and fails NoLeft4. Together with the preservation theorem, the Lean theorem b0_odd_even_chain_to_b0_NoLeft4_iff_boundary characterizes the exact output shield if and only if the guard holds under the family hypotheses.

The condition cannot be omitted from a theorem based only on NoLeft4 and the displayed local tape assumptions. The formal synthetic B/0 configuration with ones exactly at -6,-5,-3,-1 satisfies NoLeft4 and the n=0 right-side conditions, yet its actual 23-step run returns at head 3 with 1100 at -6 through -3. This example is not proved reachable from blank, so the open question is whether genuine Reach plus the odd-even hypotheses implies the boundary condition.

Source-import CI [42415186262](https://github.com/FlareZ123/bb6/actions/runs/42415186262) compiled the exact return theorems, the shield transport proofs, and the synthetic counterexample with no sorryAx. The raw 10-million-step audit found all 21/21 even-prefix, 22/22 odd-even-prefix, and 8/8 two-wave-root inputs and outputs shielded; all 22 observed odd-even inputs satisfy the boundary condition. A broader census of 7,367 reached B/0 states with left suffix 101 found only one boundary-unsafe left-six pattern, 110101. It occurs at time 3,193,243, head -689, with a right window of ten ones, then right tail 010101 beginning at h+401; it is classified as an unmatched m=401 prefix. In particular h+402=1, so it fails the odd-even terminal-zero corridor. It is not an odd-even return candidate. All 22 actual odd-even inputs have left-six pattern 010101 (21) or 000101 (one). This supports, but does not prove, the conjecture that the full reachable odd-even corridor hypotheses imply the boundary guard. The final source-import run, including the exact iff theorem and 10M audit, is [42416716883](https://github.com/FlareZ123/bb6/actions/runs/42416716883). Full proof and axiom details: [PREFIX_SHIELD_TRANSPORT.md](PREFIX_SHIELD_TRANSPORT.md).

## Ten-million-step census

The independent Node.js replay is `test-root119-two-wave-census.cjs`. It simulates 10,000,000 transitions from the blank tape and checks the predicted return time and head for each recognized macro. It observed 22,984 B/0 configurations, hence 22,983 consecutive B/0 intervals:

| First-return class | Count |
|---|---:|
| C-phase D1 return candidate | 15,198 |
| Existing odd-wave macro | 7,508 |
| Existing left-one wave macro | 177 |
| New even prefix family | 21 |
| New odd-then-even prefix family | 22 |
| Two-wave root family | 8 |
| Unmatched left-prefix candidates | 0 |
| Other | 49 |
| **Total intervals** | **22,983** |

All 51 new-family predictions agree with the raw machine replay, including both return time and returned head: 21 even-prefix, 22 odd-then-even, and 8 two-wave-root intervals. The C-phase D1 candidate is a proposed generalization of the former ten-step class. Its run-length histogram is r=2: 1, r=3: 15,176, r=4: 21. Thus the former 15,176 ten-step returns are the r=3 subfamily, and 22 further intervals have r=2 or r=4. The script asserts the complete class-count vector, the run-length histogram, and that no wave prediction remains pending at the cutoff.

### Two-wave root family: eight formerly unmatched intervals

The eight intervals previously classified as unmatched left-prefix candidates now satisfy the exact hypotheses of `b0_two_wave_root_interval_to_b0` in `Root119TwoWaveRootPrefix.lean`. In this theorem's parameterization, `n_1` is half the right-hand run of ones and `r` is the length of the alternating left retreat.

At a reached B/0 configuration with head (h), the local hypotheses are:
- (t(h-1)=1, t(h-2)=0, t(h-3)=1, t(h-4)=1);
- for every (i<r), (t(h-5-2i)=0) and (t(h-6-2i)=1);
- (t(h-5-2r)=t(h-6-2r)=0);
- the right side begins with \(2n_1\) ones, then \(0,1,0\).

The Lean theorem proves a reached B/0 return after \(8n_1+2r+30\) steps, with returned head \(h-2r-6\). Under the input NoLeft4 shield, it also proves NoLeft4 at the output and hence excludes BBad there.

The current 10M replay verifies all eight starts against these full local hypotheses, checks the predicted return time and head displacement, and checks NoLeft4 at both endpoints. The observed \((n_1,r)\) pairs are:
[
(32,2), (32,17), (32,109), (40,15), (40,46), (96,1), (176,73), (184,194).
]
The runnable audit is `test-root119-two-wave-census.cjs`; it asserts these pairs and emits the eight interval records. A further prefix-chain assertion verifies that all eight starts occur before the first unclassified B/0 interval: none has an incoming `other` or unmatched interval, and no earlier such interval occurs in its prefix from the first B/0. This makes the starts' Reach premises compositional in principle, although the macro chain has not yet been packaged as eight Lean Reach derivations. The earlier exploratory `n1` values in `FULL_RESEARCH_LOG.md` use a different parameterization and should not be read as the right-run half-length defined here.

This is a conditional theorem plus a computationally checked census. The concrete reachability of each start is supplied by the raw deterministic replay, not yet by an individual Lean `Reach` derivation. The 49 remaining `other` intervals are still unclassified.

The C-phase D1 family has a separate source-import proof in `Root119CPhaseReturn.lean`, including NoLeft4 preservation and BBad exclusion. Its 15,198 raw occurrences are checked for return time and head; see the maintained directory README for its source proof and census details.

The two-wave-root theorem and its eight-instance replay audit are summarized above; the module also contains the D-retreat shield lemma and C0/D1 odd-retreat shield theorem. See the maintained directory [README](README.md).

## Scope and next work

- The even-prefix, odd-even-prefix, and two-wave-root theorems prove exact B/0 returns under their stated hypotheses; the 51 corresponding observed intervals are checked in the 10M replay.
- The even-prefix shield theorem is unconditional under the input `NoLeft4` hypothesis. The odd-even shield theorem has the explicit three-cell boundary guard above; proving that `Reach` implies the guard, or finding a reachable counterexample, is the next question.
- Package the fully classified incoming macro prefix into Lean Reach derivations for the eight two-wave-root starts. Classify the remaining 49 other intervals and establish an all-time B/0 shield or a genuine BBad witness.
- The C-phase D1 family is now source-import verified in [Root119CPhaseReturn.lean](Root119CPhaseReturn.lean), including `NoLeft4` preservation and `BBad` exclusion; see the directory README for its separate 15,198-instance audit.
- This work is intermediate research and belongs in `im-results/`, not `results/`.
