# Even and odd-even B/0 prefix return families

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

Both statements are conditional local return theorems. They do not classify every reached B/0 configuration and do not establish a global BB(6) upper bound.

## Lean verification

Source file: `Root119OddEvenChain.lean`  
Workflow: `.github/workflows/agent42-root119-even-wave-prefix.yml`  
Successful run: [42405102264](https://github.com/FlareZ123/bb6/actions/runs/42405102264)

The workflow compiles the dependency closure from source and checks the axiom output. The relevant declarations report:

- `evenSweep_to_B_exact`: [propext, Classical.choice, Quot.sound]
- `b0_even_prefix_to_b0`: [propext, Classical.choice, Quot.sound]
- `b0_odd_even_chain_to_b0`: [propext, Classical.choice, Quot.sound]
- `b0_two_wave_prefix`: [propext, Quot.sound]

No relevant declaration depends on `sorryAx`. The local Lean 4.36.0-rc2 model proof for the even-sweep composition also compiled independently before the source-import run.


## NoLeft4 shield transport (7 November 2026)

The new source-import module [Root119PrefixShield.lean](Root119PrefixShield.lean) proves that the even prefix return preserves NoLeft4 true true false under the input shield alone. The odd-even prefix return also preserves it under the input shield plus the explicit local boundary condition

\[
\neg(t(h-6)=1\land t(h-5)=1\land t(h-4)=0).
\]

The proof follows the exact intermediate tape configurations. In the even family, the prefix exposes only cells ending in 1, the F/1 transition writes 0 after a 1, and the even D sweep has no adjacent zero pair in its swept interval. In the odd-even family, the B/1 retreat is a leftward head shift; the next F/1 write at h-3 can expose one new 1100 window, exactly the window h-6 through h-3. The boundary condition excludes it, after which the same even-sweep lemma applies.

The condition cannot be omitted from a theorem based only on NoLeft4 and the displayed local tape assumptions. The formal synthetic B/0 configuration with ones exactly at -6,-5,-3,-1 satisfies NoLeft4 and the n=0 right-side conditions, yet its actual 23-step run returns at head 3 with 1100 at -6 through -3. This example is not proved reachable from blank, so the open question is whether genuine Reach plus the odd-even hypotheses implies the boundary condition.

Source-import CI [42415186262](https://github.com/FlareZ123/bb6/actions/runs/42415186262) compiled the exact return theorems, the shield transport proofs, and the synthetic counterexample with no sorryAx. The raw 10-million-step audit found all 21/21 even-prefix and 22/22 odd-even-prefix inputs and outputs shielded; all 22 observed odd-even inputs satisfy the boundary condition. Full proof and axiom details: [PREFIX_SHIELD_TRANSPORT.md](PREFIX_SHIELD_TRANSPORT.md).

## Ten-million-step census

The independent Node.js replay is `test-root119-two-wave-census.cjs`. It simulates 10,000,000 transitions from the blank tape and checks the predicted return time and head for each recognized macro. It observed 22,984 B/0 configurations, hence 22,983 consecutive B/0 intervals:

| First-return class | Count |
|---|---:|
| C-phase D1 return candidate | 15,198 |
| Existing odd-wave macro | 7,508 |
| Existing left-one wave macro | 177 |
| New even prefix family | 21 |
| New odd-then-even prefix family | 22 |
| Unmatched left-prefix candidates | 8 |
| Other | 49 |
| **Total intervals** | **22,983** |

All 43 new-family predictions agree with the raw machine replay, including both return time and returned head. The C-phase D1 candidate is a proposed generalization of the former ten-step class. Its run-length histogram is r=2: 1, r=3: 15,176, r=4: 21. Thus the former 15,176 ten-step returns are the r=3 subfamily, and 22 further intervals have r=2 or r=4. The script asserts the complete class-count vector, the run-length histogram, and that no wave prediction remains pending at the cutoff.

The candidate's local hypotheses are: the B/0 head is at h; the r cells h-1 through h-r are ones; h-r-1 is zero; h-r-2 is one; and r≥2. The observed return law is r+7 steps to B/0 at h-r+1. The mechanism is a C/1 left scan erasing the r-cell block, followed by C/0, D/1, F/1, D/0, E/0, and A/0. The returned head lies in the erased block. This candidate has been checked against the raw replay for all 15,198 occurrences, including time and returned head, but its general Lean proof is not yet complete.

The eight unmatched left-prefix candidates have local patterns and observed times consistent with the separate two-wave-root formula (8n_1+2r+30), with head displacement (-2r-6). They remain computational matches only: the current `Root119TwoWaveRootPrefix.lean` source file has unrelated compile errors and is not importable. See the verification correction at the top of this directory's README and the broadcast warning in `communications/broadcast/`.

## Scope and next work

- The new 43 return laws prove exact B/0 returns from their stated hypotheses.
- The even-prefix shield theorem is unconditional under the input `NoLeft4` hypothesis. The odd-even shield theorem has the explicit three-cell boundary guard above; proving that `Reach` implies the guard, or finding a reachable counterexample, is the next question.
- The 8 two-wave candidates need an isolated, source-compiling proof module or repair of the existing two-wave file.
- The C-phase D1 family is now source-import verified in [Root119CPhaseReturn.lean](Root119CPhaseReturn.lean), including `NoLeft4` preservation and `BBad` exclusion; see the directory README for its separate 15,198-instance audit.
- This work is intermediate research and belongs in `im-results/`, not `results/`.
