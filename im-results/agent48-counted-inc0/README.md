# TM63 counted source macros and root-prefix candidates

**Scope.** This dossier collects original-table TM63 counted sweeps, the S1 binary-decrement/drain interface, and root-connected reset-prefix candidates. It does not establish that TM63 halts, a complete primitive-step score, or a universal six-state upper bound. All uncompiled compositions remain in `im-results/`.

## Strongest established components

### Original-machine counted sweeps

`CountedSweep.lean` proves `counted_left_sweep` and `counted_right_sweep` for the original TM63 transition table and the repository's infinite-tape `BB6Coverage.run` semantics. The theorems quantify over arbitrary tapes and preserve the complete tape outside the swept interval. The source workflow passed in [CI 42735925396](https://github.com/FlareZ123/bb6/actions/runs/42735925396); its axiom audits contain no `sorryAx`.

`M1EvenValuationBridge.lean` now kernel-checks `m1EvenValuationBridge_run`: under its explicit local tape-pattern hypotheses, the original TM63 reaches state 4 at `h+5` in exactly `12*v+23` moves, uniformly for every `v≥0` and arbitrary exterior tape. The exact committed target blob `32ba6984aae5428e5e0e316cc356042c039323f9` compiles with Lean 4.36.0-rc2; its theorem's axiom profile is `[propext, Quot.sound]`, with no `sorryAx`. This is a certified source submacro only: no root-reachability claim or full TM63 halting proof follows. See [the local preflight report](M1EvenValuationBridge-verified-submacro.md).

The local physical micro-branches are also source-certified:
- `CountedOddUnary.lean`: `counted_odd_counter`, cost `48+12*c`, for the valuation-zero local decrement pattern and arbitrary right-unary counter, with arbitrary exterior tape. [CI 42739466365](https://github.com/FlareZ123/bb6/actions/runs/42739466365); axiom audit excludes `sorryAx`.
- `CountedOneZeroUnary.lean`: the one-trailing-zero branch, cost `60+12*c`, also for an arbitrary right-unary counter. [CI 42740367928](https://github.com/FlareZ123/bb6/actions/runs/42740367928).

These are local physical templates, not yet the all-parameter S1 decrement theorem.

### Binary carry-pattern arithmetic

`CountPattern.lean` proves the carry-pattern identities and the closed form
[
\operatorname{drainPattern}(b)+12b+48
=6\cdot4^b+42\cdot2^b.
]
The theorem `BB6ChampionArithmetic.drainPattern_closed` is kernel-checked with axiom set `[propext, Quot.sound]`. This is arithmetic about the proposed sequence of valuations; it does not by itself prove that the TM63 source run realizes that sequence.

## Main source proof candidates

### Uniform all-valuation S1 decrement

`CountedCarryPrefixHRun.lean` now supplies the exact original-table carry prefix for every valuation `r≥0`. Its `HOutputShape_leftOutput` theorem derives the full left-facing `carryLeftOutputBit` identity from the counted H-run output shape; `carryPrefix_anyNonnegative_hRun` then composes the exact counted LInc H-run with the fixed 11-step B→E bridge. The prefix cost is `15+12*r`, and its contract includes the local six-cell output, the untouched right exterior, and the complete left-output stream.

`S1CarryInc0.lean` composes that prefix with the existing counted suffix to prove the canonical full S1 decrement for every `r≥0`, including `r=0`, with exact cost `48+12*r+12*b`. `S1CountedInc0.s1Config_counted_decrement` now factors any positive bounded `z<2^a` as `(2*q+1)*2^r` and uses this single all-valuation theorem, giving the endpoint `s1Config ... (z-1) (b+1)` and cost `48+12*v₂(z)+12*b`. The old odd-canonical theorem remains available as regression evidence but is no longer part of the primary decrement proof.

The new H-run, S1 composition, and unified decrement all have explicit `#print axioms` declarations and are staged in the manual `agent42-counted-lbin-dec.yml` workflow. The broader `agent42-champion-terminal-source.yml` also rebuilds the H-run dependencies before S1 consumers. The last targeted attempt, run `43858822223` at old SHA `68280aa969d8a0741848fee7d79fcbd9db9ed151`, reached the H-run and failed on three boundary-expression mismatches plus a malformed run/shape extraction. Current H-run blob `a940aab604a76a87c8ac54106616cac4e2895d43` contains the corresponding source repairs, but no fresh Lean compile has passed. The counted-LBinDec workflow now rejects `sorryAx` and `native_decide`; the exact local source preflight remains pending. Earlier local interface harnesses used deliberately axiomatized imported source interfaces; they are not a source-closure proof.

### All-ones S1 drain

`S1CountedDrain.lean` instantiates the generic CountedReset drain using the uniform all-valuation S1 decrement candidate. Its intended theorem is
[
\operatorname{run}\ tm2\ (\operatorname{drainCost}(2^k-1,c))\
\quad(\operatorname{s1Config}\ L\ n\ m\ a\ (2^k-1)\ c\ h)\
=\operatorname{some}(\operatorname{s1Config}\ L\ n\ m\ a\ 0\ (c+2^k-1)\ h).
]
For `c=0`, the proposed exact cost is
[
6\cdot4^k+42\cdot2^k-12k-48.
]
The source module, the generic prefix-then-drain adapters, and their axiom gates are present, but the complete original-import workflow has not yet passed. Treat the drain as a proof candidate until the full transitive audit succeeds.

### Marker-1 even-valuation source increment

`M1EvenValuationSource.lean` states a general original-table source macro for
every \(0<n<2^L\) and positive left counter \(a\). It factors
\(n=(2q+1)2^v\), proves the S1-to-q4 prefix run at cost
\(12a+12v+32\), composes the q4 suffix/reset prefix at cost \(35+3b\),
and then invokes the counted all-ones drain. Its exported
`m1EvenValuation_counted_increment_source` has the exact
`proposedIncrementCost 1 n a b` run type and ends at
`s1Config L (n-1) 0 (a+b+2) 0 (2^b-1) (h+5+3*b)`.

For marker 1, the declared cost unfolds to
\(6\cdot4^b+42\cdot2^b+19+12(a+v_2(n))-9b\).

This theorem is a reusable source-level macro, **not itself a blank-root theorem**.
It is already consumed by `TM63RootMiddle34.lean` for authentic-root row 32
and by `TM63SourceIncrementDispatcher.lean` for the general marker-1 branch.
Those compositions remain intermediate until their exact closures compile and
their axiom profiles pass; no halting claim follows.

The exact acceptance target is the complete import closure of
`M1EvenValuationSource.lean`, with axiom profiles for its five exported
q4/reset/counting declarations and no transitive `sorryAx`. The focused
`m1-even-valuation-source.yml` workflow remains a leaf diagnostic (one root,
five M1 profiles) that isolates this module if another root fails. The existing
`agent42-champion-terminal-source.yml` `middle34-acceptance` target now also
checks the same five M1 profiles plus the M2/root declarations, enforces the
standard axiom allowlist, and rejects `native_decide` in the exact closure.
It is the strict integrated acceptance gate. The standalone leaf workflow
has also been strengthened to enforce the same axiom allowlist and reject
`native_decide`; its remaining distinction is diagnostic isolation. Consolidate
it into the existing family workflow after the replacement is validated, or
retain it only if that isolated failure mode proves useful. Reuse these two
surfaces only; do not add another parallel workflow. The first manual workflow attempt (run
`44910559991`) stopped in the then-current `S1CarryOutputBridge.lean`; that
source has since been repaired, but the old run is not evidence for the patched
revision. Agent 8 also replaced the hand-written \(N+4\)/far-tail branch in
the private left-facing proof with the exact-parent-type footprint lemma in
`M1EvenValuationBridgeFootprint.lean` (commit
`dbef928d34d8887328a880c80a05e7e48bf6f6e4`). The integrated source closure
has **not** been recompiled after these changes, so this remains intermediate
work in `im-results/`; do not promote it or treat its theorem as accepted.

### Generic all-odd m=0 increment

`M0OddGenericSource.lean` is a new source-level generalization of the m=0 reset row to every odd `n=2*k+1`. It frames the existing `n=5` q4 prefix on the half-line `x≥h-(3*a+7)`; the base head bound is stronger, and both the source input prefix and generic cut prefix have length `3*a+8`, so the arbitrary tail `binDec (L-1) k` aligns exactly after the finite bridge. The generic cut stream is `[true] ++ d1pow (a-1) ++ markerWord 2 ++ d0 ++ d1 ++ binDec (L-1) k ++ lh`, after which the existing q4 suffix and counted drain yield the exact m=0 increment.

This theorem interface subsumes the m=0 odd residue-one, residue-five, and residue-seven specializations; those files are retained as independent regression evidence. The middle-15 root wrapper now instantiates the generic theorem at `n=16*r+1`. **The new generic module and updated root wrapper are not yet compiled or axiom-audited.**

### Conditional champion adapter

`S1ChampionCountedReset.lean` specializes the terminal composition interface and removes its generic `hInc0` premise, conditional on a genuine blank-root run and a source reset-prefix run. It does not prove either machine-specific run. Its local interface checks used stubs; the repository source closure still needs its manual workflow and `sorryAx` audit.

## Authentic-root reset-prefix candidates

The initial root itself is established separately: [`RootSourceBridge.lean`](../agent48-root-witness/RootSourceBridge.lean) kernel-checks the original-machine run of 27,959 moves from blank to `s1Config 3 7 2 6 0 63 29`, with a full infinite-tape embedding and no `sorryAx`. That theorem is only the initial prefix.

The following later compositions remain candidates:

| Module | Intended source transition | Current evidence boundary |
| --- | --- | --- |
| `TM63RootQ4Drain.lean` | Compose the 27,959-move root witness, the 332-move q4 prefix, and the 63-bit all-ones drain. The candidate endpoint is `s1Config 3 6 1 71 0 (2^63-1) 223`; the candidate successful-move count is `6*4^63 + 42*2^63 + 27487`. | The complete original-import composition and transitive axiom audit have not passed. This is not a halt proof or an attained BB(6) lower bound. |
| `M1EvenQ4Prefix.lean`, `M1EvenQ4Suffix.lean`, `TM63M1EvenRootComposition.lean` | The next `(m,n)=(1,6)` reset row, followed by the counted drain, to `(m,n)=(0,5)`. | The old focused CI run 43397674787 failed before downstream suffix modules. Subsequent source repairs have not passed a fresh complete compile/axiom audit. |
| `M2EvenSixQ4Prefix.lean`, `M2EvenResidueSix.lean` | For every admissible `n=16k+6`, prove the `m=2` reset prefix to `m=1,n=16k+5`, with counter `2^b-1` ready for the counted drain. | The old targeted run 43659498187 predates the current repairs. The base finite-boundary/index repairs are at commit `58906b7b7a45ea7c309ec61996c5163ce3238e03`; the lifted residue-six boundary repairs are at `88754f3885817f13924aa68459d3e98384a29bc9`. Neither current file has passed compilation. Agent 42 owns the leaf acceptance check; do not edit these files concurrently. |
| `M0EvenFourQ4Bridge.lean`, `M0EvenFourQ4Prefix.lean`, `M0EvenResidueFour.lean`, `M0EvenResidueFour-bridge-candidate.md`, and Agent 8's `im-results/agent8-root-residue-four/TM63RootResidueFour.lean` | The next row after the proposed middle-11 endpoint: `m=0,n=16r+4 → m=2,n=16r+3`, with the general residue parameter `n=8k+4`. | The 51-step finite bridge, base `L=3,n=4` source-prefix run, intermediate-head bound, arbitrary-tail half-line lift, q4 interfaces, M0-specific suffix/drain composition, and Agent 8's root-through-middle-13 wrapper are present as Lean drafts. The derived candidate increment count is `proposedIncrementCost 0 (8*k+4) a b + 9*b = 6*4^b + 42*2^b + 12*a + 39`. None has been compiled; these remain conditional source-proof candidates, not a certified root extension. |
| `M1EvenResidueTwoSource.lean` | For every admissible `n=8k+2`, prove the `m=1` counted increment to `m=0,n=8k+1`, with the q4 reset prefix followed by the all-ones drain. | The source theorem reuses the existing n=6 q4 prefix via a sharp half-line `run_frame` lift; it does not need Agent 8's new 40-step bridge. The exact prefix and counted-increment statements are in [M1EvenResidueTwoSource.md](M1EvenResidueTwoSource.md). The module and manual CI gate are present but uncompiled; it is not yet connected to a root itinerary. |
| `TM63RootResidueTwo.lean` | Append the `m=1,n=16r+2` residue-two counted increment to the candidate blank-root endpoint after middle 13, reaching `m=0,n=16r+1` (middle 14). | The root arithmetic supplies `k=2r`, the width bound, and positive counter length. The composition is documented in [TM63RootResidueTwo.md](TM63RootResidueTwo.md), with a manual CI/axiom gate after the middle-13 wrapper. It is uncompiled and remains conditional on both imported source modules. |
| `M0OddGenericSource.lean`, `TM63RootResidueThree.lean` | Append the generic odd-`n` marker-0 source increment at `n=16r+1`, reaching marker 2 and `n=16r` (middle 15). | The generic theorem uses the base `n=5` q4 prefix and its public head bound; the root wrapper now calls this theorem instead of the narrow residue-one module. Both are source drafts only, uncompiled and unaudited. |
| `M2EvenResidueSixteen.lean`, `M1OddResidueSeven.lean`, `TM63RootResidueSixteen.lean` | Compose the `m=2,n=16r` row (`n=32k+16`) and the `m=1,n=16r-1=8q+7` row (`q=4k+1`), reaching the middle-17 state `m=0,n=16r-2=32k+14`. | Agent 41 supplies the source increments; Agent 49's root wrapper composes middle 15→16→17. These remain uncompiled and unaudited. Agent 41's `TM63RootResidueZero` / `TM63RootMiddle17` are an alternative composition. |
| `M0EvenFourteenQ4Bridge.lean`, `M0EvenFourteenQ4Prefix.lean`, `M0EvenFourteenHeadBound.lean`, `M0EvenFourteenGenericSource.lean`, `TM63RootMiddle18.lean` | Lift the middle-17 holdout `m=0,n=32*k+14` to arbitrary `L≥5`, increment to `m=2,n=32*k+13`, and compose the root through candidate middle 18. | Agent 49 supplies the 39-step base bridge and `L=5,n=14` q4 prefix. Agent 48 supplies the `h-(3*a+9)` head bound, generic source-level q4-prefix/suffix/counted-drain theorem, and middle-18 root wrapper. Written but not compiled or audited. |
| `M2OddGenericStage.lean`, `TM63RootMiddle19.lean` | Append the generic odd `m=2` counted increment at `n=16*r-3=32*k+13`, reaching `m=1,n=16*r-4` (candidate middle 19). | Agent 42's `m2Odd_counted_increment_source` already covers every odd bounded `n`; Agent 48 adds the root composition from middle 18. The wrapper is written and staged in CI but uncompiled/unaudited. |
| Agent 41's `M1EvenResidueFourBridge.lean`, `M1EvenResidueFourQ4PrefixRun.lean`, `M1EvenResidueFourSource.lean`, plus Agent 48's `TM63RootMiddle20.lean` | Append the generic `m=1,n=8*q+4` counted increment at `q=2*r-1`, i.e. `n=16*r-4`, reaching `m=0,n=16*r-5` (candidate middle 20). | Agent 41 supplies the 53-step finite bridge, base q4 prefix, arbitrary-width half-line lift, q4 suffix split, and counted-drain source candidate. Agent 48 adds the authentic-root wrapper. None of these Lean modules has been compiled or axiom-audited. A separate JS replay is saved at `M1EvenResidueFourIndependentAudit.mjs`; the equivalent checks passed 756 small parameter cases, which is finite corroboration only. |
| `M0OddGenericSource.lean`, `TM63RootMiddle21.lean` | Reuse the generic m=0 odd counted increment at `n=16*r-5`, reaching `m=2,n=16*r-6` (candidate middle 21), the input family needed before Agent 42's m=2 residue-two row. | The generic all-odd source theorem already covers this row; Agent 48 adds only the authentic-root composition. The source theorem's full original-import closure and the new wrapper remain uncompiled/unaudited. |
| Agent 42's `M2EvenResidueTwo.lean`, `M2EvenResidueTwoCounted.lean`, plus Agent 48's `TM63RootMiddle22.lean` | At `q=2*r-1`, append the `m=2,n=8*q+2` counted increment at `n=16*r-6`, reaching `m=1,n=16*r-7` (candidate middle 22). | Agent 42's general source prefix and counted-drain adapter are present; Agent 48 adds the authentic-root composition. The source modules and root wrapper remain uncompiled/unaudited. Agent 42's detailed dossier should be updated to reflect that the Lean draft now exists. |
| `M1OddResidueOneSource.lean`, `TM63RootMiddle23.lean`, and the fixed `M1OneQ4Prefix.lean` | Middle 23: marker 1, `n=16*r-7=8*(2*r-1)+1`, to marker 0, `n=16*r-8`. | The arbitrary-width q4-prefix lift, suffix/reset-prefix composition, counted-drain theorem, and authentic-root wrapper are now written. The source explicitly imports `S1CountedDrain`; the manual M1 workflow stages the full H-run/S1 decrement closure. None of these modules or their transitive dependencies has yet passed a current Lean compile/axiom audit. The 756-case replay remains finite corroboration only. |
| `M0EvenEightQ4Bridge.lean` and `M0EvenEightQ4Prefix.lean` | Next after middle 23: marker 0, `n=16*r-8=8*(2*r-1)`, to marker 2, `n=16*r-9`. | The exact 63-step finite bridge on `[-15,3]`, its all-odd-quotient input match, and the generalized q4-prefix run are now written. The prefix costs `60+12*a = 9*a+63+3*(a-1)` and ends at state 4 at the original head. The q4 suffix target-left identity is also stated. The q4 cut's left-facing/right-shape/far-tail proofs and counted-drain/root composition are still open; no Lean compile or axiom audit has passed. |

The candidate source chain is now staged through middle 23 (the middle-18 through middle-23 edges are still uncompiled and unaudited):
`blank → middle 13 → middle 14 → middle 15 → middle 16 → middle 17 → middle 18 → middle 19 → middle 20 → middle 21 → middle 22 → middle 23`.
The middle-17 state is
`S1(tm63Length1,16*r-2,0,A17,0,B17,H17)`, where the root arithmetic rewrites
`16*r-2 = 32*k+14 = 8*(4*k+1)+6`. The next required row is therefore the difficult marker-0 even sector `n=8*q+6` with `q=4*k+1`.

Agent 49 has now supplied a source-exact 39-step local bridge and an `L=5,n=14` q4 prefix in [`M0EvenFourteenQ4Bridge.lean`](../agent49-m0-even-residue14/M0EvenFourteenQ4Bridge.lean) and [`M0EvenFourteenQ4Prefix.lean`](../agent49-m0-even-residue14/M0EvenFourteenQ4Prefix.lean). The prefix cost is `36+12*a`. Agent 48 added [`M0EvenFourteenHeadBound.lean`](M0EvenFourteenHeadBound.lean), a separate, uncompiled head-bound helper for that base run: the head stays at or to the right of `h-(3*a+9)`, split across the 3a counted left sweep, the 39-step bridge with relative window [-9,2], and the 3(a-1) E-scan.

The middle-18 source increment is now written in `M0EvenFourteenGenericSource.lean`. It lifts the `L=5,n=14` prefix to every `L≥5`, `n=32*k+14`, and `32*k+14<2^L`, using the exact `3*a+10`-cell source/target prefixes and their common tail
`[true] ++ d0 ++ d0 ++ d1 ++ binDec (L-5) k ++ lh`.
It then composes the q4 suffix (cost `39+3*b`) and counted drain, yielding the source-level increment to `S1(L,32*k+13,2,a+b+1,0,2^b-1,h+5+3*b)`. The base q4 prefix costs `36+12*a`; the reset-prefix total is `75+12*a+3*b`.

Agent 48's head-bound helper is a separate dependency proving `h-(3*a+9) ≤ head` throughout the base `36+12*a` run. The main `agent42-champion-terminal-source.yml` workflow now stages Agent 49's bridge/prefix and compiles the head-bound and generic source modules with `sorryAx` gates. **No CI has been dispatched and none of these new source modules has passed Lean compilation or transitive axiom audit.** The middle-18 and middle-19 root wrappers are staged in `TM63RootMiddle18.lean` and `TM63RootMiddle19.lean`; the new middle-20 wrapper is not yet integrated into that workflow. The immediate acceptance work remains the base bridge, head bound, generic source theorem, middle-17 wrapper, and middle-18/19 consumers. The next source row after middle 19 is `m=1,n=16*r-4=8*(2*r-1)+4`. Agent 41's `M1EvenResidueFourSource.lean` now gives an arbitrary-width source-level candidate for every `n=8*q+4`, and Agent 48's `TM63RootMiddle20.lean` instantiates it at `q=2*r-1`. This is only a candidate: the new bridge, prefix, generic source theorem, and root wrapper remain uncompiled and unaudited. Agent 41's detailed statement and proof architecture are in [the residue-four dossier](../agent41-m1-even-residue4/README.md); an independent finite-support JavaScript replay is preserved in `M1EvenResidueFourIndependentAudit.mjs`. The existing generic all-odd m=0 theorem then takes `n=16*r-5` to `m=2,n=16*r-6`; `TM63RootMiddle21.lean` records this composition. That module is also uncompiled. Agent 42's m=2 residue-two source row is now composed at the same quotient `q=2*r-1` in `TM63RootMiddle22.lean`, reaching `m=1,n=16*r-7`; this imported row and root wrapper are also uncompiled. The marker-1 residue-one source row is now written in `M1OddResidueOneSource.lean`: it lifts the fixed n=1 prefix to arbitrary admissible n=8*q+1, composes the q4 suffix and S1 counted drain, and is instantiated by `TM63RootMiddle23.lean`. The 756-case replay remains finite corroboration only. The source and root wrapper have not passed a current original-import compile or transitive axiom audit.

Agent 41's finite replay of `n=8*q+6` at `q=1,a=1,b=0,1,2` and widths `L=4,5,8,12` survived a 200,000-step horizon. This is exploratory simulation only; it is not the authentic root configuration (whose `L,A17,B17` are different), and it proves neither halting nor nonhalting. The replay and its width caveat are in [Agent 41's holdout dossier](../agent41-m0-even-root-holdout/README.md).

The separate M2 residue-six branch still has theorem `m2Even_residue6_q4_reset_prefix_source` with endpoint
`S1(L,16k+5,1,a+b+2,2^b-1,0,h+5+3b)`
and prefix cost `83+12a+3b`. Composing the generic all-ones drain would yield
`S1(L,16k+5,1,a+b+2,0,2^b-1,h+5+3b)`; this separate branch remains uncompiled and should not be confused with the current middle-17 continuation.

## Conditional 0101 boundary alternate (not an authentic root continuation)

`P2ActualBoundaryComposition.lean` is retained as a conditional source theorem for the distinct input family `1^(m+2) ++ 0101 ++ 1^7 ++ 00 ++ tail`. Its internal namespace and theorem names now say `Alternate0101`; the file is not connected to the authentic TM63 root. The corrected `frameAt` semantics make the actual second q4Tail residual `1^(m+2) ++ 0100 ++ tail`, with the tail beginning `100`. The authentic q4Tail-to-S0 tape identity remains the open handoff documented in [Agent 38's root-q4tail dossier](../agent38-root-q4tail/README.md); only that interface may be composed with Agent 44's `p2S0Drain_q4Postlude`.

## Critical unresolved obligations

1. Pass the full original-import Lean 4.36.0-rc2 compile and transitive `sorryAx` audit for `CountedCarryPrefixHRun.lean`, `S1CarryInc0.lean`, `S1CountedInc0.lean`, and `S1CountedDrain.lean`; in particular, audit the new all-valuation H-run and its left-output identity.
2. Validate the current M0 residue-seven and Rst1Prime/Bridge8 dependency closures. The first Rst1' instance is wired into the root source path, but the post-patch Bridge8→Bridge30 chain still needs its source/axiom gate.
3. Pass the source/axiom gate for the middle-15 generic all-odd m=0 increment and its root wrapper, then the middle-16 M2-even residue-sixteen row and middle-17 M1-odd residue-seven row.
4. Compile and transitive-axiom-audit the residue-14 bridge/prefix, `M0EvenFourteenHeadBound.lean`, `M0EvenFourteenGenericSource.lean`, `TM63RootMiddle18.lean`, and `TM63RootMiddle19.lean`; fix actual proof errors before making any root-level claim.
5. Compile and transitive-axiom-audit Agent 41's m=1 residue-four bridge/prefix/source modules, Agent 48's `TM63RootMiddle20.lean`, the `M0OddGenericSource.lean` → `TM63RootMiddle21.lean` continuation, and Agent 42's `M2EvenResidueTwo` → `TM63RootMiddle22.lean` composition; the 756-case replay is not a substitute for source acceptance.
6. Compile and transitive-axiom-audit `M1OddResidueOneSource.lean` and `TM63RootMiddle23.lean` with their complete original imports. The source lift, q4 suffix, counted-drain composition, and root wrapper now exist; the M1 manual workflow stages the all-valuation H-run/S1 decrement closure and must reject transitive `sorryAx`.
7. Compile and audit the separate M2 residue-six, M0-even residue-four, Agent 8 middle-13, and M1-even residue-two source branches. They remain useful candidates but are not substitutes for closing the current root continuation.
8. Prove the original-machine primitive-step count for the entire halting itinerary, including the final halting-query convention. Independently, prove a universal six-state upper bound.

The Coq macro formulas and the arithmetic score candidate are not substitutes for these original-source run proofs. No exact BB(6) value, complete champion halt certificate, or global maximality theorem is claimed here.

## Historical material

The former chronological dossier is preserved at [`history/README-chronology-20261115.md`](history/README-chronology-20261115.md). Use it for detailed derivations and superseded attempts.


## Middle-23 update (2026-11-16)

The marker-1 residue-one source row and authentic-root wrapper have now been written:
- `M1OddResidueOneSource.lean` lifts the fixed `L=3,n=1` q4 prefix to all admissible `n=8*q+1), proves the q4 suffix/reset-prefix, and composes the S1 counted drain.
- `TM63RootMiddle23.lean` specializes the row at `q=2*r-1), extending the candidate source itinerary from middle 22 to middle 23 with endpoint `S1(tm63Length1,16*r-8,0,A23,0,B23,H23)`.
- A missing direct import of `S1CountedDrain` in the source module has been corrected. The manual workflow now includes the actual all-valuation H-run/S1 decrement/drain dependency closure and checks its axiom output.

These remain source-level candidates: no current Lean compile or transitive `sorryAx` audit has passed. The next source row is marker 0, even `n=8*q` with `q=2*r-1`; Agent 48's prior handoff assigned that row to Agent 42. Do not duplicate it. The middle-23 wrapper also depends on the still-uncompiled middle-22 chain.


## Post-middle-23 M0-even row (2026-11-16)

The next root successor is the odd-quotient family `S1(L,8*q,0,a,0,b,h)`, with `q=2*r-1`. The new intermediate source files are:
- `M0EvenEightQ4Bridge.lean`: a `decide`-checked 63-step finite TM2 bridge, head confinement to `[-15,3]`, and an input-match theorem for every admissible odd quotient. The low counter identity is `binDec(L,8*q)=d1^3 ++ d0 ++ binDec(L-4,q/2)`; only the first two cells of the final `d0` block are read by the bridge.
- `M0EvenEightQ4Prefix.lean`: composes the `3*a)-cell counted sweep (9a moves), the 63-step bridge, and a `3*(a-1))-step E-scan. The resulting source-level q4 prefix has cost `60+12*a` and ends in state 4 at the original head. It also states the target-left identity for the q4 suffix.

The finite base is the first admissible quotient `q=1` (`L=4,n=8`), not the full `L=3,n=0` source. A direct replay of the latter halts for `a=1,b=0`; it is therefore not used as a whole-run base. The generalized bridge uses the common finite window for all odd q. The q4 cut's left-facing, right-shape, and far-tail interfaces are not yet proved, so no reset-prefix/count-drain theorem or middle-24 root wrapper is claimed. Both new modules are uncompiled and unaudited.

## M0 even-eight source row: draft, not yet compiled

The next source row after root middle 23 is
`S1(L, 8q, 0, a, 0, b, h)` with odd `q`. The draft
`M0EvenEightGenericSource.lean` attempts to close the q4 cut completely:

- left-facing stream: the swept prefix is all ones; the 19-cell bridge window
  reads `markerWord 2 ++ d0^4 ++ d1`; the remaining source tail aligns at
  absolute left index `3*a+16`;
- right-facing shape: the head and first right cell are established by the
  sweep, the next cells and unary block are inherited from the S1 source,
  and the complete blank tail begins at right offset `9+3*b`;
- q4 suffix: the shared `Q4RightEndpoint` theorem consumes those complete
  interfaces;
- exact reset-prefix cost: `resetPrefixCost 0 (8*q) a b = 99+12*a+3*b`,
  using `v2(8*q)=3);
- proposed full increment cost:
  `6*4^b + 42*2^b + 12*a - 9*b + 51`.

The target source theorem is
`S1(L,8q,0,a,0,b,h) -> S1(L,8q-1,2,a+b+1,0,2^b-1,h+5+3b)`
with the original `proposedIncrementCost`. The companion
`TM63RootMiddle24.lean` composes this row after middle 23, where
`q=2*r-1`.

**Status:** both Lean files are drafts only. They have not passed a focused
local compile or an original-source CI check and are not evidence for a new
BB(6) bound. Agent 6 has been asked to compile the exact dependency closure.
The existing `agent42-counted-lbin-dec.yml` source-check workflow has been
extended for this row, but dispatch is being held pending that preflight.

A deterministic standalone simulator is now preserved at
`m0_even_eight_source_sim.js`. It transcribes the original TM2 table and
checks 1,890 bounded parameter cases (`4<=L<=9`, odd
`1<=q<2^(L-3)`, `1<=a<=6`, `0<=b<=4`). For every case it checks the
q4-prefix state/head and exact set of all nonblank tape positions across the full left/right support, the 39+3b q4
suffix endpoint, the counted drain endpoint, and the closed total cost.
All 1,890 cases passed in the V8 execution used to produce this note.
This is reproducible computational evidence only; it does not replace the
source-level Lean proof or establish a global BB(6) upper bound. The
existing manual source-check workflow now also runs this simulator.


## Valuation-uniform M0-even 8q counted-source draft

The all-valuation marker-0 row `n=8q`, `q>0`, now has a complete **source-level** Lean composition. It remains uncompiled and unaudited; it is not yet an accepted theorem or a blank-root result.

The chain is:
- `M0EvenEightValuationSource.lean`: the valuation-dependent prefix run, cost `60+12*a+12*v₂(q)`;
- `M0EvenEightValuationQ4Source.lean`: exact left-facing cut word, q4 right shape, blank far tail, and q4-suffix composition, with reset-prefix cost `99+12*a+12*v₂(q)+3*b`;
- `M0EvenEightValuationCountedSource.lean`: the final counted-drain wrapper, exporting `m0EvenEight_valuation_counted_increment_source`.

Under `q>0`, `4≤L`, `8*q<2^L`, and `a>0`, the counted theorem declares the original-table run from
`s1Config L (8*q) 0 a 0 b h`
to
`s1Config L (8*q-1) 2 (a+b+1) 0 (2^b-1) (h+5+3*b)`,
using `proposedIncrementCost 0 (8*q) a b` primitive steps. Its exact cost is
`6*4^b + 42*2^b + 12*a + 12*v₂(q) - 9*b + 51`.

The construction retains the reproducible 288-case exact-tape probe and 101 parameterized finite-bridge checks described in [the derivation note](M0EvenEightValuationExtension.md). Agent 42 corrected the false marker-length objection using the actual four-bit `markerWord 2`; Agent 4 independently checked the dynamic coordinate partition symbolically in [the coordinate review](../../communications/agent48/20261118T121242Z_agent4-m0-valuation-coordinate-review.md). These checks support source review, not kernel acceptance.

The existing manual workflow `.github/workflows/agent42-counted-lbin-dec.yml` now stages and compiles the three new source modules after their dependencies and checks the final exported theorem output for forbidden axioms. It has not been dispatched. The exact import closure must first pass local Lean 4.36.0-rc2 preflight, followed by inspection of the complete transitive `#print axioms` profile; reject `sorryAx`, `native_decide`, and custom axioms.

**Scope:** this is only the local marker-0 `n=8q` S1 counted-increment premise for the TM63 24-cycle. It does not prove that the authentic blank-root orbit reaches these S1 configurations, does not establish a halt witness, and does not determine BB(6). It is distinct from the root-connected marker-0 `n=8q+4` residue-four row.


## Marker-1 even-L q4 checkpoint macro (intermediate)

See Marker1TerminalQ4Macro.md, Marker1TerminalArithmetic.lean, marker1_terminal_q4_macro.py, and marker1_terminal_q4_checkpoint.py. The z=0 family has a full-tape simulator-checked checkpoint/cycle decomposition, and Lean proves the resulting valuation-sum and runtime arithmetic. Positive-z experiments retain the left binary-countdown frame but exhibit nested right-side counters and only conjectural event-count laws. The authentic m=2,n=1 root endpoint has z=2^b-1>=3, so the z=0 law is not yet a root closure. No BB(6) value or universal upper bound is claimed.


The sparse 64-cell-block C++ simulator marker1_terminal_q4_block_sim.cpp extends the positive-z checkpoint experiments to multi-billion-step limits while checking the complete left checkpoint frame. The revised nested event-count conjecture and the 7-billion-step z=2 observation are documented in Marker1TerminalQ4Macro.md.


The sparse 64-cell-block C++ simulator marker1_terminal_q4_block_sim.cpp extends the positive-z checkpoint experiments to multi-billion-step limits while checking the complete left checkpoint frame. The revised nested event-count conjecture and the 7-billion-step z=2 observation are documented in Marker1TerminalQ4Macro.md.


New positive-z first-cycle evidence: for z=1..4, the measured q4 cycle cost matches C1(z)=drainCost(2^z-1)+12(2^z+z+6)+2, independent of A,L in tested cases; q4-event counts match 6*4^(2^(z-1)-1)+2. These remain computational macro conjectures pending a source-level proof. The z=4 case was checked through a 6.44-billion-step cycle.


The positive-z first-cycle experiments now match a counted-drain law for z=1..4, including a verified 6,443,827,286-step first cycle at z=4. See Marker1TerminalQ4Macro.md for the formula, data, and the still-open source-level proof obligation.


## Positive-z first-checkpoint setup composition (2026-11-19)

A new intermediate setup decomposition is documented in
[PositiveZCheckpointSetupDecomposition.md](PositiveZCheckpointSetupDecomposition.md).
It formalizes the corrected suffix order
`B20 ; sweep(L+1) ; B9 ; sweep(A+1) ; B6 ; sweep(z) ; B30`,
with fixed bridge kernels in `PositiveZCheckpointSetupBridges.lean`
and conditional tape-side composition in
`PositiveZCheckpointSetupComposition.lean`.

The residual context has the equivalent forms
`11 ++ (010)^(A+1) ++ 011 ++ 110 ++ (010)^L ++ 011 ++ 101 ++ 11`
and
`110 ++ (100)^(A+1) ++ 111 ++ (100)^(L+1) ++ 1110111`.
The new source drafts reduce the final left/right tape equality to the
suffix guards and two blank exterior-tail conditions from the preceding
S0 scans/B8 bridge.

The dependency-free simulator
`verify_positive_z_setup_decomposition.js` passes 1,047 finite parameter
triples (maximum 4,861 simulated steps). This is finite evidence only.
**All new Lean composition declarations remain uncompiled** pending local
Lean 4.36.0-rc2 preflight; do not treat them as accepted source theorems or
promote this material to `results/`.


## Root-to-first-q4 checkpoint composition (2026-11-19)

The new intermediate source file
[`TM63RootFirstQ4Checkpoint.lean`](TM63RootFirstQ4Checkpoint.lean)
composes Agent 44's authentic blank-root-to-marker-1-S0 endpoint with
Agent 42/24's `firstQ4Checkpoint_run`. It uses the exact input bound
`2^b-1 < 2^(exponent+b+2)` and `RootShift.shift_run` to translate the
first q4 frame from head zero to the actual root head. The exported
`tm63_blank_reaches_first_q4_checkpoint` statement preserves the exact
primitive-step count and returns the translated q4 finite frame.

**Status:** source-level composition draft only; the complete dependency
closure has not been compiled or axiom-audited. It is not a new accepted
halting-time result. Agent 42's
`FirstQ4P1FrameBridge.lean` already identifies its first q4 frame with the
canonical P1 checkpoint and proves the marker-1-S0-to-second-frame run;
the blank-root-to-first-frame join is the new part here.

The exact CI 44438791470 diagnostic exposed two residual integer-coordinate
side conditions in `M1EvenState1Sweep.state1_three_left`. Both have been
patched in the live source (commit
`3b4787ea945e2d0d1c6302412957b6e21dd4ef6f`) using explicit `omega`
inequalities. The patch has not yet passed local Lean preflight. Agent 12
has been asked to run the exact current-main `middle34-acceptance`
dependency closure, following Agent 44's request; Agent 42 has also been
asked for a narrow local preflight.

The alternative `PositiveZCheckpointSetupRootCycle.lean` proof remains a
modular source draft of the Rst1' setup stage; its `binDec_allOnes` zero
branch now includes `binaryCounterFuel`. The current
`FirstQ4CheckpointPrePostlude.lean` pipeline still uses the existing
`rst1Prime_counted_macro`, so the alternative setup module is not yet
integrated and should not be mistaken for an accepted replacement.

Next: obtain the local compile/axiom report for the M1 patch; review and
compile the new root-to-first-q4 composition; only then compose the root
with Agent 42's P1/second-frame continuation. Keep all these items in
`im-results/` until the exact source closures pass.


### Extension through the second q4 frame

`TM63RootSecondQ4Frame.lean` composes the same authentic root-to-marker-1-S0
prefix directly with Agent 42's `firstQ4P1Root_to_secondFrame` theorem. It
uses the root-derived bounds `0 < A`, `z < 2^A`, and `3 ≤ z`, then
translates the full first-q4/P1 continuation to the absolute root head.
The resulting `tm63_blank_reaches_second_q4_frame` theorem is a stronger
source-level exact-run draft than the first-checkpoint theorem.

**Status:** also uncompiled. It is a compositional trajectory result, not a
proof that TM63 halts or a determination of BB(6). The first-q4 and
second-q4 files should be compiled only as a later, narrow endpoint
acceptance target after the current middle34/M1 gate passes.

## Positive-z q4 outer-counter descent

A new intermediate arithmetic interface is recorded in [Q4OuterCounterDescent.md](Q4OuterCounterDescent.md). Agent42's [outer-width recurrence](../agent42-q4-s0-drain/FirstQ4P1OuterWidthRecurrence.lean) now exposes the P2 100 guard after every two-d0-block boundary and the corresponding A → A-2 residual counter. This makes the arithmetic outer loop finite (residual A in {1,2}) if the actual q4Tail/S0 trajectory is shown to consume the six-cell suffix each time. The q4Tail-to-S0 tape identity and six-cell trajectory invariant remain open. The A=2 boundary now has a separate z=1 diagnostic: [A2TerminalBaseCaseZ1.md](A2TerminalBaseCaseZ1.md) records exact finite runs to SectionBits and identifies a distinct 11110000 branch when the P2 100 guard fails. This does not close the authentic root's positive-z terminal case (z≥3), and no halting claim follows.


## Exact tape interface for the m=2,n=4 q4 prefix (2026-11-23)

Added `m2EvenSix_q4_prefix_data_exact`, which upgrades the existential tape witness in `m2EvenSix_q4_prefix_data` to the concrete `m2EvenSixQ4CutTape`. The proof uses the established left- and right-facing stream characterizations to show extensional equality of the existential witness and the explicit tape. Downstream M2 residue-six consumers can now use a concrete exact-run interface rather than relying on an invalid `rfl` across an opaque existential theorem. The theorem compiled successfully in targeted run 45288313701. The downstream M2EvenResidueSix consumer still has later head-bound, run-composition, and frame/tape obligations; its complete source closure is not yet accepted.
