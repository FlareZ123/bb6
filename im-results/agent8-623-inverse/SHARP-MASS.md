# Cryptid #623: sharper source-rooted counter-mass growth

Agent 8, 2026-11-03. Intermediate source-connected mathematical result. **Does not decide the blank-origin halting question or the exact BB(6) value.**

## The source and state

The original [Cryptids module](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean) is pinned at SHA `c86f15861709b76042998c5211c7b2f83991621b`. It supplies `evalA`, `drainB`, `highLevelNext` and a raw Turing-machine-to-accelerator halting equivalence. The accelerator states are `D(a,d)`, the genuine blank start is `D(0,7)`, and a surviving step is `T(D(a,d))=some(D(a',d'))`.

Agent49's source theorem `next_strict_mass` gives the uniform, sharp increase `a'+d' >= a+d+7`; `run_preserves_even` gives even `a` at every genuine surviving blank-origin return; `run_grows_at_least_seven` gives `a_n+d_n>=7(n+1)`. Agent8's preceding `TernaryBudgetSource.lean` proves `drainB` third-counter growth `d' >= d+3b` and characterizes equality.

## New proof chain

- [SharpMassSource.lean](SharpMassSource.lean) establishes `a'+d' >= a+d+9` whenever `a` is even and at least 4.
- [SharpMass10Source.lean](SharpMass10Source.lean) establishes `a'+d' >= a+d+10` whenever `a` is even and at least 6, even when `d=0`.
- [SharpMass12Source.lean](SharpMass12Source.lean) establishes `a'+d' >= a+d+12` whenever `a` is even, `a>=6` and `d>0`.
- [RootedMassSource.lean](RootedMassSource.lean) certifies `a_{n+2}+d_{n+2} >= a_n+d_n+17` for every surviving true blank-origin pair with `n>=2`.
- [RootedMass19Source.lean](RootedMass19Source.lean) sharpens that pairwise assertion to `a_{n+2}+d_{n+2} >= a_n+d_n+19` for all `n>=2`, conditional on both endpoint states existing. Its additional exact formulas force any low first counter to escape into the `a>=6,d>0` sector at the next surviving step.

The 19-unit proof is a finite split on the first counter and the initial second counter. If `a>=6,d>0`, the first step contributes at least 12, and the second contributes at least 7. If `a<=4`, with `a+d>=16`, a successful step has `a'>=6,d'>0`; its subsequent successful step therefore contributes at least 12. If `a>=6,d=0`, the mass threshold forces `a>=16`, and the exact first step is `D(a-4,14)`, placing its successor in the 12-unit domain. The unconditional seven-unit bound applies to the other step in each case.

The low-counter escape theorem uses the following exact formulas on the indicated mass domain (all expressed as accelerated, successful transitions):

| Initial state, domain | Exact successor |
| --- | --- |
| `D(0,d)`, even `d>=16` | `D(d,7)` |
| `D(0,d)`, odd `d>=17` | `D(d-1,14)` |
| `D(2,d)`, even `d>=14` | `D(d,9)` |
| `D(2,d)`, odd `d>=15` | `D(d+1,10)` |
| `D(4,d)`, even `d>=12` | `D(d-6,23)` |
| `D(4,d)`, odd `d>=13` | `D(d+1,12)` |
| `D(a,0)`, even `a>=16` | `D(a-4,14)` |

All transitions are obtained by symbolic unfolding of the source's ternary evaluator and B-drain, including explicit nonzero guard checks.

The true blank orbit begins `D(0,7), D(6,14), D(6,31)`. Consequently a second induction gives, for every `k>=0` and every surviving indicated section visit:

```text
run(2k+2)=D(a,d)   =>   a+d >= 37+19k
run(2k+3)=D(a,d)   =>   a+d >= 44+19k
```

These are *conditional* growth theorems. A future transition can still halt at a large counter value, and the theorems provide no universal lower bound on the length of the actual TM computation.

## Calibration and limits

The single-step bounds are sharp on their respective domains:

- `D(4,1) -> D(2,12)` gains exactly 9.
- `D(6,0) -> D(2,14)` gains exactly 10.
- `D(6,3) -> D(0,21)` gains exactly 12.

The 19-unit two-step lower bound has not been proved optimal. A finite independent exact Python scan over even `a<450`, `0<=d<800`, and `a+d>=16` suggested a **minimum pairwise gain of 21**, achieved by `D(10,6) -> D(2,28) -> D(28,9)`; the scan is only a finite discriminator, without a universal lower-bound theorem.

## Verification provenance

- Direct source imports, with `#print axioms` and no `sorry`, use the exact original DeepMind Cryptids module and the previous authenticated Agent49/Agent8 theorems.
- [Original-source CI 41735987839](https://github.com/FlareZ123/bb6/actions/runs/41735987839) **succeeded** on the +9 and +10 proofs at pinned upstream SHA.
- [Original-source CI 41737171715](https://github.com/FlareZ123/bb6/actions/runs/41737171715) **succeeded** on the initial rooted 17-per-pair theorem and exact low escape. Later 17-slope closed forms were appended after the passing head and require subsequent re-verification.
- The 12-unit and 19-unit modules compiled locally under Lean 4.36.0-rc2 with a duplicate source-matched accelerator and, for direct-source imports, with local proof-interface surrogates; that *local* compilation alone does not authenticate upstream compatibility. The direct-source proof-chain verification is [run 41738901856](https://github.com/FlareZ123/bb6/actions/runs/41738901856), which is pending at the time of this writing. Check its eventual outcome before claiming the new source-imported results fully independently certified.
- A separate [initial 12-unit job 41738140354](https://github.com/FlareZ123/bb6/actions/runs/41738140354) failed before theorem compilation due to an installer PATH omission (`lake: command not found`), not a reported mathematical proof failure. The complete 19-unit verification workflow explicitly invokes the pinned compiler paths.

All work remains in `im-results/` pending independent novelty evaluation and direct connection to a blank-reachable obstruction. **BB(6) remains open.** A useful next target is a source-verifiable 21-unit pair bound or a root-reachable exclusion within Agent49's logarithmically narrow halting gate. The second target is more closely aligned with an eventual actual #623 halting decision.
