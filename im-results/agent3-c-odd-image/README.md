# Agent 3: Exact Machine C return-map image and a blank-origin dyadic exclusion

**Status (2026-11-02): Unmodified-source Lean 4.36.0-rc2 CI verified, intermediate result.** Machine C and BB(6) are unresolved. The repository retains the source in `Agent3CImage.lean` and `Agent3C14.lean`; `.github/workflows/agent3-c-odd-image.yml` is manually triggered and has no push/commit trigger.

## Source-proved global bounce invariant

For the **original** `BB6.Agent46.bounce`, every successful output `some (x,y)` satisfying `y>=4` obeys
```
(x+y) % 4 = 0 ∨ (x+y) % 4 = 3.
```
This is a strong-induction theorem over the decreasing high counter. For an odd middle counter the final bounce sum is `2*k+6 ≡ 0 mod4`; for an even middle counter and final height at least four, the sum is `2*k+7 ≡ 3 mod4`. Recursion preserves the final output and strictly decreases the high counter. The exceptional even `c=4` branch outputs height 3, outside this theorem.

**The original-source complete section map:** Every successful `BB6.Agent46.secNext (a,k)=some (x,y)` with `y>=5` odd has sum in `{0,3} mod4`. This follows from the bounce invariant plus complete, explicit enumeration of direct section branches. On the authentic blank-origin orbit starting at `(5,1)`, we thus exclude at **every time** all points
```
(4*u+2, 4*(v+1)+3)    (u,v : Nat).
```
The newly excluded family consists of `x≡2(mod4), y≡3(mod4), y>=7`. This is a global, all-natural invariant, not a finite simulation or a density estimate.

## Smallest dyadic halting target

`Agent3C14.lean` imports the **unmodified Agent38SectionParity** proof `bounce_positive` to establish that `secNext` never emits `(3,1)` from any state. The strengthened bounce-image theorem rules out `(1,4)` as a bounce output. All direct branches are enumerated, leaving the **unique** possible input `(3,1)` to an output `(1,4)`. Since the initial state is `(5,1)`, `(3,1)` is unreachable from the authentic blank section, and hence so is `(1,4)`.

This eliminates the depth-zero `a=1` stopping target of Agent46's source-certified exact dyadic stopping basin; the infinitely many other stopping targets remain unclassified. In particular, no proof of Machine C nonhalting is claimed.

## Exact source-level Lean verification

[Successful manual GitHub Actions run 41441884283](https://github.com/FlareZ123/bb6/actions/runs/41441884283), source checkout commit `12041bf8eb00cd6ac82b849e38f56ab921384e46`, source-odd-image job `125265508225`.

The workflow compiles the complete unchanged Agent11 `CLine`, Agent8 `GenericSection` and `CSectionTotal`, Agent21 `CReachBridge`/`CPhaseRank`, all exact Agent46 prerequisite modules including `BounceCalc`, `BounceProof` and `FastSectionDef`, plus **unmodified** Agent38 `Agent38SectionParity`. It then compiles Agent3's two source files against those imports. Every step completed successfully. The final `#print axioms` output for `section_no_31`, `section_14_requires_31`, `blank_no_31`, `blank_no_14` lists only `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.

Earlier [successful run 41440848197](https://github.com/FlareZ123/bb6/actions/runs/41440848197) independently verified the initial weaker odd-height theorem. The later run verifies its strengthened replacement.

## Scope and next mathematical bottleneck

The exact Machine C blank halting equivalence is already provided by Agent46 and Agent21's original-machine bridges and can be combined with the now-proved exclusion of `(1,4)`. The surviving infinite stopping-depth families require a forward blank-reachability language, or a genuinely unbounded inverse proof, to resolve. A useful next step is to examine source predecessors of `(1,k)` for all depths in the dyadic stopping equation; the source restriction eliminates every bounce predecessor when `k≡0(mod4)`, but the direct predecessor `(k-1,k/2-1)` remains when `k>=4`. Even this reduction leaves infinitely many admissible parameter values and is **not** a closure theorem.

This work is retained under `im-results/` because it does not yet give a full holdout decision or an academically publishable BB(6) frontier result.
