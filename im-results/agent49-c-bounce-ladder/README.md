# Agent 49: exact all-depth Machine C bounce arithmetic

**Status 2026-11-02 11:02 UTC:** Intermediate source-certified mathematical statements. Machine C's authentic blank-orbit stopping status, all five known BB(6) holdouts, and exact BB(6) remain **open**. Store here in `im-results/`; do not promote to `results/` without a genuine externally novel/global theorem.

## Source semantics and new theorems

The original source is the **unmodified** `im-results/agent11-c-line/CLine.lean` definition `BB6CLine.nextC`. Agent 46 has independently proved a complete exact zero-third-counter section in `im-results/agent46-c-jump/{JumpHigh,JumpMacro,JumpSection,JumpBounce,JumpOneReturn,JumpBounceSections,BounceCalc,BounceProof,FastSectionProof}.lean`. The present work adds closed all-depth formulas and an exact exponential criterion to that existing recursive machinery.

1. **Odd bounce ladder**, `Ladder.lean`. If `k%2=1`, define `K(0)=k`, `K(n+1)=2K(n)+3`, accumulated depletion `D(0)=0`, `D(n+1)=D(n)+2K(n)+3`, and elapsed time `T(0)=0`, `T(n+1)=T(n)+2K(n)+4`. For all naturals with `D(n)+4<=c`:
   ```
   run T(n) (some (0,k,c)) = some (0,K(n),c-D(n)).
   ```
   The Lean kernel verifies `K(n)+3=(k+3)*2^n`, `D(n)+3n+2k=2K(n)`, `T(n)+2n+2k=2K(n)`, and `T(n)=D(n)+n`. Single bounce consumes exactly `2k+4` steps when the next high-sector state remains live.

2. **Even-start section return**, `LadderSection.lean`. Starting from any `(a,k,0)` with `a>=2`, `a` even and `a<=2k`, the exact `a-1`-step high descent is followed by `n` full odd bounces and a last partial odd bounce. The endpoint is a new `c=0` section in precisely **`2k+n+2` original accelerated calls**, subject to the exact remaining-third-counter window in the Lean theorem `even_section_ladder`. This is a closed parameterized formula, supplementing Agent46's pre-existing recursive general section.

3. **Even bounce ladder**, `EvenLadder.lean`. For even middle counter `k`, let `KE(0)=k`, `KE(n+1)=2KE(n)+4`, `DE(0)=0`, `DE(n+1)=DE(n)+2KE(n)+5`, `TE(0)=0`, `TE(n+1)=TE(n)+2KE(n)+3`. Whenever `DE(n)+4<=c`:
   ```
   run TE(n) (some (0,k,c)) = some (0,KE(n),c-DE(n)).
   ```
   In particular, `run (TE(n)+2) (some (0,k,DE(n)+5))=none` for every even `k` and natural `n`: an exact infinite **synthetic halting family**. The familiar Machine C Thin gateway `(0,2j,4j+10)` is the `n=1` subfamily with `k=2j`. These synthetic inputs are not claimed blank-reachable.

4. **Complete classification of Agent46's recursive bounce halts**, `BounceParity.lean`. The kernel proves, for every natural `k,c` with `c>=4`:
   ```
   (BB6.Agent46.bounce k c).2 = none
     <-> k%2=0 && exists n,
           c+2*k+3*n+3 = (k+4)*2^(n+1)
   ```
   (`&&` above is expository; Lean theorem uses logical conjunction.) Thus **odd-middle bounces never halt within the bounce episode**; even-middle ones halt exactly at the stated exponential Diophantine locations. Proof uses complete strong induction on `c`, reflecting every branch of the **original unmodified** Agent46 recursive `bounce`; `KE`, `DE` closed forms; and independently verified local CLine step sequences. Here `bounce k c` returns the number of accelerated calls and an option pair: its `none` means this bounce episode halted before returning to `c=0`. Subsequent execution after `some` is outside this criterion.

## Verification

Original-source manual-only workflow `.github/workflows/agent49-c-bounce-ladder.yml` imports exact `CLine.lean` and Agent46's unchanged bounce source and compiles all Agent49 modules in Lean 4.36.0-rc2:

- [CI 41431408426](https://github.com/FlareZ123/bb6/actions/runs/41431408426): odd ladder passed.
- [CI 41431862699](https://github.com/FlareZ123/bb6/actions/runs/41431862699): even-start section return passed.
- [CI 41432575802](https://github.com/FlareZ123/bb6/actions/runs/41432575802): even ladder and synthetic halting family passed.
- [CI 41433296165](https://github.com/FlareZ123/bb6/actions/runs/41433296165): full original Agent46 recursive bounce arithmetic classification passed, including all prior modules.

The final `#print axioms` reports only standard Lean axioms `[propext, Classical.choice, Quot.sound]` or a subset. No `sorryAx`, mocks, `admit` or `native_decide` in the committed artifacts. A locally written `BounceCalc.lean` clone was used solely to speed test compilation; final CI uses **unchanged Agent46 source** instead, and the local clone is never committed.

## Research implications and remaining work

The newly closed bounce equation could be substituted into Agent46's full section map to produce a direct, nonrecursive arithmetic test for the *next* zero-third-counter return. For instance, in the high-bounce region `a>=2, a<2k`, the initial descent lands at `(0,a-1,2k-a+3)` so a bounce halt requires `a` odd and `2k+a+4+3n=(a+3)*2^(n+1)`. Prove this fully and compose it with Agent46's exact section and the authenticated blank entry if it improves the global inverse problem. This is a prospective algebraic deduction, not yet a committed theorem.

The central BB(6) challenge persists: characterize the actual blank-origin sequence's section coordinates, exclude every reachable Diophantine halting gate, or construct a genuine blank-origin halting witness. Neither increasing arithmetic explicitness nor excluding additional finite/modular targets alone decides Machine C. Also note Agent11's globally exact Thin reduction; our local arithmetic criterion must be reconciled with that prior characterization before any global claim.
