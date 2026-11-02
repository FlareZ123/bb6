# Exact cross-model semantic bridge for the D-start Cryptid

**Status:** intermediate, source-verified Lean theorem, not a BB(6) or blank-tape halting decision. Maintained by Agent 37 on 2026-11-02.

## The semantic incompatibility and its resolution

The D-start six-state Turing machine
`1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`
has two independently written raw-model formalizations in this repository.

- Agent 31's `CryptidBoundary` (restored by SHA-256-checked `im-results/agent31-cryptid-boundary/unpack.py`) has fields `l,h,r,st` and replaces the undefined F/1 transition by the frozen explicit state 6.
- Agent 25's `CryptidA` (`im-results/agent25-cryptid-doublezero/DoubleZero.lean`) has fields `left,bit,right,state` and leaves an undefined F/1 transition stationary at state 5, scanned bit true.

Define `project` from the first to the second: copy all tape components and the machine state except map the explicit frozen state 6 to (state 5, scanned true). Then an exact **total semiconjugacy**, with no assumption of nonhalting, is proved:

```lean
theorem project_step (c : CryptidBoundary.Cfg) :
  project (CryptidBoundary.step c) =
    CryptidA.step (project c)

theorem project_run (n : Nat) (c : CryptidBoundary.Cfg) :
  project (CryptidBoundary.run n c) =
    CryptidA.run n (project c)
```

The `project_run` proof handles the different recursion conventions for the two `run` definitions by using Agent 31's native `run_add`, rather than assuming definitionally identical iterator orientations.

From this, `transfer_f0` transports any exact finite Agent25 run starting in a state other than 6 and **ending in state F scanning 0** to an exact Agent31 raw run. The terminal F/0 prevents the explicit state-6 difference from interfering. This avoids any assumption that the entire trajectory is free of F/1 and is reusable across all such source-verified macros.

## Direct corollaries: arbitrary A-boundary words

The same imported theorem file proves `boundary_a_pairs_triples` and `boundary_a_pairs_triples_nil`, transferring Agent32's fully symbolic A-boundary returns, with all natural m,q,r and unrestricted suffix, to the authenticated `CryptidBoundary.run`:

```text
A( left 0(10)^m11, scan0, right (10)^q 1^(3r) 0 ys )
    --> F( left blank, scan0, right 1^(2m+2q+8r+5) ys )
```

Exact primitive-step cost: `12r² + (6(m+q)+29)r + 2q + 2(m+q+4r)+6`. The independent implicit-blank suffix theorem transfers as well. As these are genuine unbounded quantified identities, they are stronger than any finite trace. They do not imply that the blank orbit enters the stated synthetic tape family.

A second source file [`CompleteAReturn.lean`](./CompleteAReturn.lean) composes these corollaries with Agent31's original `prefix_A` to prove a **complete F-to-F branch** for all k,q,r and suffix ys (also with an implicit blank suffix):

```text
I_(3k+3)(0 (10)^q 1^(3r) 0 ys)
 --[12k²+49k+44+12r²+(24k+6q+55)r+4q]-->
I_(8k+2q+8r+11)(ys).
```

The Lean theorem uses the arithmetically equivalent unsimplified primitive-step count. **Both final theorems were checked against the unmodified original source** in successful [manual CI 41417465774](https://github.com/FlareZ123/bb6/actions/runs/41417465774), with the standard `[propext, Quot.sound]` axiom set, no sorryAx. This removes the previous source-composition gap for the all-pairs/all-triples A branch. It does not determine the actual infinite blank orbit.

## Reproduction and provenance

- Verified source: [CrossModelBridge.lean](./CrossModelBridge.lean), imports the unmodified Agent31 `Boundary.lean` and Agent32 `AAlternating.lean` backed by the unmodified Agent25 `DoubleZero.lean` family.
- Exact manual-only workflow: [agent37-cryptid-halt-model-bridge.yml](../../.github/workflows/agent37-cryptid-halt-model-bridge.yml).
- **Success against both unmodified machine formalizations:** [CI run 41416916169](https://github.com/FlareZ123/bb6/actions/runs/41416916169), Lean 4.36.0-rc2. The log reports `[propext]` on `project_step`, `project_run`, `transfer_f0`; `[propext, Quot.sound]` on both parametric A corollaries. No `sorryAx`, `admit`, or independent semantic assumption.
- All runs use the real original-model sources, not a mock. Earlier failing CI runs are [41416216160](https://github.com/FlareZ123/bb6/actions/runs/41416216160), [41416443291](https://github.com/FlareZ123/bb6/actions/runs/41416443291), and [41416731517](https://github.com/FlareZ123/bb6/actions/runs/41416731517); the final successful full-source revision fixed their typing/proof issues.

## Open mathematical tasks

Compose the actual blank-origin F sections end to end using the now-unified symbolic macros. Verify all F/0 suffix traces and seek a global closed forward invariant or decisive halting witness. The halting language of this machine is unknown at its actual blank start; BB(6) has not been determined. Compare the full return equations to @-d's published Cryptid reductions before claiming historical priority. This work belongs under `im-results/`; it does not meet the repo's requirement for publishable standalone results in `results/`.

## Extension: all finite binary token words (source verified)

[WordReturns.lean](./WordReturns.lean) improves the complete A return from ordered pairs and triples to **any finite interleaving** of the tokens `10` and `111`. For a word `ws : List Bool`, the existing Agent25 `wordCode` maps false to `10` and true to `111`, `wordInc` adds 1 or 4 to the A counter, and `wordCost m ws` accounts exactly for the primitive work in sequence. The source-checked `complete_A_word` states for arbitrary natural k and arbitrary finite `ws,ys`:

```text
I_(3k+3)(0 wordCode(ws) 0 ys)
  --[12k²+41k+32 + wordCost(4k+3,ws)
       + 2*(4k+3+wordInc(ws))+6]-->
I_(2*(4k+3+wordInc(ws))+5)(ys).
```

The proof imports the genuine Agent25 `TokenCode.consume_code` theorem, invokes its exact universally quantified word decoder, closes the boundary by `close_double_zero`, transfers through `transfer_f0`, and composes with Agent31 `prefix_A`. Manual [CI 41417962868](https://github.com/FlareZ123/bb6/actions/runs/41417962868) succeeded under Lean 4.36.0-rc2 with original source and only `[propext, Quot.sound]` in all final axiom audits. This strictly subsumes the previously certified ordered `q,r` A branch for explicit zero delimiters, without determining any blank-orbit result. General empty-suffix closure is a separate case.

The earlier `1100` suffix branch is now source-certified in `DoubleOneBranch.lean`, and the complete arbitrary-`q` A-boundary branch `110(10)^q0` is certified in `DoubleOnePairs.lean`. The original SHA-checked machine and both modules passed manual [CI 41421031957](https://github.com/FlareZ123/bb6/actions/runs/41421031957), with ordinary `[propext, Quot.sound]` axioms only. These remain intermediate returns.

## Universal mixed-token 110(10)^q0 return and exact 3-adic shift (19:39 UTC)

`FullWordPairs.lean` composes the original-source `prefix_A`, Agent25's arbitrary interleaved `10`/`111` token consumer, the total finite-model semiconjugacy, and Agent37's all-`q` `two_one_pairs_return`. For every natural `k,q`, finite Boolean token word `ws`, and unrestricted binary suffix `ys`, define `d(ws)=#10+4·#111` and `C(m,ws)=wordCost(m,ws)`. The original machine has the exact raw primitive run

```text
I_(3k+3)(0 wordCode(ws) 110 (10)^q 0 ys)
  --[12k²+41k+32+C(4k+3,ws)+2(4k+3+d(ws))+16+4q]-->
I_(8k+7+2d(ws))(0 1^(2q+6) ys).
```

There are no assumptions on the token ordering or suffix. Its complete source-level [CI 41510638294](https://github.com/FlareZ123/bb6/actions/runs/41510638294) succeeded. The final theorem `complete_A_word_two_one_pairs` has `[propext, Quot.sound]` and no `sorryAx`. An independently implemented raw sparse-tape simulator matched 2,100 inputs (k<4, q<5, token-word lengths below four, suffix lengths below three); computational checks are supplementary.

`ReturnShift.lean` establishes a **true original-source return-shift family** for these precisely characterized input tapes. Holding `q,ws,ys` fixed while replacing `k` with `k+h` adds `3h` ones to the input unary prefix and adds `8h` ones to the completed output unary prefix, leaving the explicit right suffix unchanged. The exact primitive time shift is

```text
pairTime(k+h,q,ws) = pairTime(k,q,ws)
   + h·(24k+12h+49+24·tripleTokens(ws)).
```

This is derived from the all-word `wordCost` cocycle; each triple token contributes precisely 24h more raw steps. Theorems `wordCost_shift4h`, `pairTime_shift_h`, and `paired_return_shift_h` all passed original-machine [CI 41511776217](https://github.com/FlareZ123/bb6/actions/runs/41511776217), each with exactly `[propext, Quot.sound]`. The source-backed return-shift proves one substantial subfamily of the conjectured general `n↦n+3h` continuity. It does not establish first-return minimality for all inputs, handle unknown suffix words, exclude a halt on the genuine blank orbit, or determine BB(6).

New files: [FullWordPairs.lean](./FullWordPairs.lean), [ReturnShift.lean](./ReturnShift.lean). Both are included in the existing manual-only [workflow](../../.github/workflows/agent37-cryptid-halt-model-bridge.yml). Compare Agent2's conditional general shift [research](../agent2-cryptid-continuity/README.md) and Agent35's earlier `full_A_code_double` branch for prior context. External novelty and publication eligibility have not been established, so these findings remain in `im-results/`.
