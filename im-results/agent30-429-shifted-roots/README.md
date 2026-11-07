# Four source-certified shifted terminal cylinders for BB429

**7 November 2026.** This is an intermediate machine-specific result, **not a decision of machine #429 or BB(6)**. The full unchanged-repository Lean 4.36.0-rc2 proof chain passed [source CI 42347188987](https://github.com/FlareZ123/bb6/actions/runs/42347188987). A separate original Google DeepMind Cryptids pinned raw-machine audit is [run 42347463517](https://github.com/FlareZ123/bb6/actions/runs/42347463517); check its actual conclusion before claiming that additional bridge passed.

## Result and exact quantifiers

Let \`BB429.run n (0,0)=some (a,b)\` be the **actual blank-root** trajectory under the exact local arithmetic accelerator for six-state Cryptids machine \`1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA\`. Its unique halting gateway is \`b+1=2*a\`. In [BB429ShiftRays.lean](BB429ShiftRays.lean), four theorems state, for **every natural** \`n,a,b\`, that an authentic \`run\` state on this line satisfies:

| First-counter forbidden congruence | Full family proved unreachable, every \`q∈ℕ\` | Proof declaration |
| --- | --- | --- |
| \`a % 32768 ≠ 765\` | \`(32768*q+765, 65536*q+1529)\` | \`blank_halt_not_765_mod_32768\` |
| \`a % 32768 ≠ 3281\` | \`(32768*q+3281, 65536*q+6561)\` | \`blank_halt_not_3281_mod_32768\` |
| \`a % 262144 ≠ 2385\` | \`(262144*q+2385, 524288*q+4769)\` | \`blank_halt_not_2385_mod_262144\` |
| \`a % 131072 ≠ 16381\` | \`(131072*q+16381, 262144*q+32761)\` | \`blank_halt_not_16381_mod_131072\` |

These exclude the single **previously surviving representatives 765, 3281, 2385, and 16381** among the original 255 survivors at modulus 262144 after Agent 1's 673-cylinder exclusion. On the exact prior common baseline of 58 terminal residues mod 16384 (928 lifts at mod 262144), the combined exclusion grows from **673 to 677**, leaving **251 necessary candidates** under this composition. This is a count of arithmetic constraints, *not* a claim that any survivor occurs or that a still-unresolved machine has been decided. The four families overlap previously excluded finer-modulus rays. Their distinct new content against that baseline is exactly the four named representatives.

## Proof mechanism

The new proof reuses Agent 30's earlier [all-parameter, source-sound affine inverse certifier](../agent30-429-even16/BB429InverseKernel16.lean), whose \`cert_sound\` theorem proves nonreachability simultaneously for **all quotient parameters \`q\`** whenever a finite symbolic inverse tree closes. As in Agent 1's earlier [four split rays](../agent1-429-four-split/BB429FourSplit.lean) and Agent 33's [five shifted rays](../agent33-429-five-shift/README.md), a ray with coefficient \`A\` is divided into \`q=0\` and \`q=k+1\`. The second case is shifted to \`(A*k+(A+r),2*A*k+(2*A+2*r-1))\`, at which the *unchanged* depth-16 \`BB429Kernel16.cert\` evaluates to \`true\` in Lean's kernel.

The four zero-quotient targets are ruled out by exact successful blank-root checkpoints together with Agent 5's all-time strictly increasing \`rank(u,w)=2*u+w\`, using a rank-straddle lemma credited to Agent 1. No sampled finite time cutoff is assumed to decide unbounded reachability.

| Target \`(a,b)\` | Rank \`2a+b\` | Genuine crossing macro time \`k\` | \`run k\` | \`run (k+1)\` |
| --- | ---: | ---: | --- | --- |
| \`(765,1529)\` | 3059 | 638 | \`(9,3040)\` | \`(21,3019)\` |
| \`(3281,6561)\` | 13123 | 3171 | \`(25,13073)\` | \`(53,13020)\` |
| \`(2385,4769)\` | 9539 | 2246 | \`(3069,3396)\` | \`(0,9544)\` |
| \`(16381,32761)\` | 65523 | 16107 | \`(16396,32722)\` | \`(0,65524)\` |

Lean checks the first three straddles by \`decide\` and the fourth using sixteen exact 1,000-step checkpoint blocks to avoid elaborator recursion-depth limits. The proof derives all-natural exclusions from authentic \`run\` and \`cert_sound\`. It uses no \`sorry\`, \`native_decide\`, substitute successor map, or unverified machine simulation.

## Verification and provenance

- [Source audit 42347188987](https://github.com/FlareZ123/bb6/actions/runs/42347188987): **successful**. Selective workflow [.github/workflows/agent30-429-shifted-roots.yml](../../.github/workflows/agent30-429-shifted-roots.yml) compiled the original local accelerator, all prior root predicates, \`BB429InverseKernel16\`, and the new \`BB429ShiftRays\` file with Lean 4.36.0-rc2. Final \`#print axioms\` audited; \`sorryAx\` rejected.
- [SourceRawHaltShift.lean](SourceRawHaltShift.lean) transports all four genuine-source exclusions to the unchanged **original Cryptids six-state machine** through the established source bridge, and composes them with the previously native-certified 673-cylinder raw halting equivalence. The [pinned native-source workflow](../../.github/workflows/agent30-429-shifted-native.yml) checks the original Google DeepMind repository at \`c86f15861709b76042998c5211c7b2f83991621b\` under Lean 4.35.0-rc4; its completion status must be checked separately.
- Temporary local interface preflight compiled the new proof structure with original signatures supplied as axioms and an exact definition of the inverse certifier. **This preliminary test is not cited as a complete proof.** The successful repository-source audit above is the decisive verification for the genuine local accelerator.

## Why the result matters, and limits

The source all-parameter inverse kernel can fail at low affine offsets even when the entire positive-parameter tail is certifiable. A finite exact blank-root rank argument then discharges the finitely many missing boundary cases, producing universal exclusions. This specific split technique and both major components are prior project work; this module supplies four previously surviving precise applications and a native raw-source theorem under evaluation. These are **intermediate research refinements** with unconfirmed external mathematical novelty, appropriately stored under \`im-results/\`.

The complement still contains infinitely many terminal parameter families. The exact BB(6) maximum and a certified nonhalting decision for machine #429 remain open. Future proof effort should prioritize an all-time authentic-root return invariant, a complete history-sensitive physical-tape characterization of the last one-sided excursion, or a full machine-level decision; endlessly subdividing finite-modulus residues cannot by itself solve that quantifier.
