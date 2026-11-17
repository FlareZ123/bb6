# TM63 champion reset arithmetic and counted source coverage

**Current status — 17 November 2026: BB(6) remains unresolved.** The exact blank-root prefix to the published S1 configuration after 27,959 original TM63 transitions is kernel-checked in the Agent 48 root dossier. The subsequent TM63 middle countdown is not yet source-certified end-to-end, and no universal six-state upper bound or exact maximal runtime proof exists.

## Current middle-countdown bottleneck

The `sectionResult` countdown changes the index by \(n\mapsto n-1\) and the marker by \(m\mapsto(m+2)\bmod 3\). Its source dispatcher has 24 residue/marker classes because \(\mathrm{lcm}(8,3)=24\). The current repository has source-theorem declarations for **22 of those 24 classes**:

- marker 1: the new all-index `m1EvenValuation_counted_increment_source` covers all eight residues;
- marker 0 and marker 2: the generic odd-index source theorems cover all four odd residues each;
- markers 0 and 2: the even-residue-2, -4 and -6 source theorems cover the six nonzero even residues.

The only missing all-q families are **marker 0, \(n=8q\)** and **marker 2, \(n=8q\)**. The existing marker-0 `q`-odd theorem covers only \(v_2(n)=3\); the marker-2 `n=32k+16` theorem covers only the \(v_2(q)=1\) subfamily. The root-connected 24-cycle genuinely needs both all-q extensions on alternating cycles: with `K=tm63RootMiddleK` odd, cycle `j` has marker-2 quotient `q₂=K-1-3j` and marker-0 quotient `q₀=K-2-3j`, whose parities alternate and whose even valuations are not fixed.

The following files isolate the exact proof boundary:

- [24-cycle source coverage and dispatcher contract](TM63-24Cycle-Source-Coverage-20261117.md): the complete rotated class table, current theorem mapping, root quotient formulas, and the arithmetic needed to dispatch all 24 cases.
- [Conditional 24-class dispatcher](TM63SourceIncrementDispatcher.lean): an uncompiled Lean integration candidate. Given exactly the two all-q residue-zero source theorems, it constructs the total one-step macro and applies `sectionResult_run_of_source_macro` to obtain the full `sectionResult` original-machine run. The nonzero-residue wrappers also accept quotient zero, so no extra small-index base cases are needed.
- [M2 residue-zero source-to-q4 derivation](M2EvenResidueZero-SourceIntegration-20261117.md): exact factorization, H-run premises, q4 source-left word, right shape, and cost decomposition for the missing marker-2 row.
- [Generic H-run left-facing lemma](LBinDecHRunLeftFacing.lean): an uncompiled proof candidate showing the H-run's `d1pow n ++ d0 ++ tail` to `d0pow n ++ d1 ++ tail` transformation.
- Agent 48's [M0 even 8q all-valuation proof plan](../agent48-counted-inc0/M0EvenEightValuationExtension.md) and its encoding, fixed-prefix, sweep, suffix, and macro helper modules.

**Validation boundary:** the 22 existing declarations are not yet one accepted dependency closure; the conditional dispatcher, generic H-run left-facing lemma, and M2 source integration remain uncompiled drafts. No CI result is claimed for these new files. The repository's manual-only source workflows should be run only after an exact local Lean 4.36.0-rc2 preflight is clean. The local shell/runtime was unavailable during this update, so no preflight or CI dispatch was performed.

**Next decisive steps:** complete the marker-0 and marker-2 all-q source theorems; compile and axiom-audit the exact combined dispatcher closure; instantiate it at the authentic blank-root parameters; then connect the resulting endpoint to the remaining reset/terminal source itinerary. Even a completed lower-bound path would not solve BB(6) without the separate universal six-state upper bound.

## Historical development and established narrower results

**Agent 24, 2026-11-03, R005.** The original arithmetic facts below were checked in Lean 4.36.0-rc2. The Lean file [ChampionModular.lean](ChampionModular.lean) requires only `Lean.Elab.Tactic.Omega`, no mathlib, axioms, `sorry`, or replacement machine semantics. These results are **not** a new BB(6) bound, champion step-count certificate, rooted-machine decision, or a source-integrated Coq-to-Lean proof.

## Source-certified exact physical sweep counts

The [Lean source](CountedSweep.lean) now proves two **universally quantified counted submacros for the original TM63 transition table and the original infinite-tape `BB6Coverage.run` semantics**, with no copied-machine-model premise. Both compile through the existing manual [champion-root workflow, CI 42735925396](https://github.com/FlareZ123/bb6/actions/runs/42735925396); the printed axiom audits contain only standard Lean axioms, no `sorryAx`.

* `counted_left_sweep`: for arbitrary tape `T`, head position `h`, and natural `n`, if `T(h+1)=0` and `T(h-i)=1` for every `0≤i<n`, the D-state physical run after exactly `3*n` successful moves is at head `h-n`, back in D, with the complete tape `sweptLeft n T h`. Its local base case `counted_three_left` moves one zero left across one marked cell in exactly three primitive actions.
* `counted_right_sweep`: for arbitrary tape `T`, if each of the `n` three-cell blocks starting at `h+3*i` contains only ones, exactly `3*n` successful moves return to D at head `h+3*n`, with the entire tape `sweptRight n T h`. Its base case `counted_three_right` performs the exact three-cell source scan.

These are source-sound full-tape step-count identities usable as components of a champion cost proof.

**New all-length source theorem (10 November 2026).** [`CountedOddUnary.lean.xz.b64`](CountedOddUnary.lean.xz.b64) (readable copy: [`CountedOddUnary.lean`](CountedOddUnary.lean)) establishes `BB6Coverage.Agent48Champion.counted_odd_counter` under the original 12-entry TM63 table, original full infinite-tape `run`, and any natural right-unary counter `c`. Starting from the explicit physical odd-decrement input `oddCounterInput T` (D/head0, fixed local binary-zero-tail and separator), assume exactly the `3(c+1)` consecutive marked right-counter cells at positions `7..9+3c` and zeros at `10+3c,11+3c,12+3c`; all other exterior tape data is arbitrary. The theorem proves exactly **`48+12*c` successful primitive transitions**, ending in D/head0 with a completely specified infinite tape `oddCounterOutput c T`. The proof splits into a fixed 15-step prefix, `3(c+1)` source E-scanner steps, a four-step zero turn, `3(5+3c)` source D-sweep steps, and a fixed eleven-step return. It proves the necessary full-tape structural intermediate invariants, including the collapse of the one-block zero-moving sweep to a two-cell update. This discharges the arbitrary-right-counter cost term for the **valuation-zero** micro-branch of the previously conjectural `48+12*v₂(z)+12*c`. The branch is characterized by its physical local bits; a fully general `S1(...,z,c)` source encoder and positive binary valuation induction remain open.

**One-trailing-zero source branch (10 November 2026).** The separate [`CountedOneZeroUnary.lean.xz.b64`](CountedOneZeroUnary.lean.xz.b64) module (readable copy: [`CountedOneZeroUnary.lean`](CountedOneZeroUnary.lean)) is the all-`c` counted local template for the one-trailing-zero (`v₂(z)=1`) decrement branch, with cost `60+12*c` (commit `4484337a`). Its `even_counted_odd_counter` theorem starts from the exact local `d0 d1` tape pattern (marks `[-5,-2,-1,0,2,3,4]` around head 0); its 27-step `even_prefix15` trace changes that prefix to `d1 d0`, then composes the common right-unary suffix. The pinned original-table Lean workflow checks decompressed SHA-256 `0d1acc16c377f17e3f2c624a74f9874bafdf255f2fcdc9749c9d00c83b4f6737` and compiles the module; manual run [42740367928](https://github.com/FlareZ123/bb6/actions/runs/42740367928) succeeded at workflow source revision `6d2ef8d9`. This is a checked local template, not a general published-`S1` encoder or the `v₂(z)≥2` cases. A deterministic TM63 simulation suggests a `15+12r` prefix for arbitrary carry length r=1..5; only r=1 is Lean-proved. See [CarryPrefixExperiment.md](CarryPrefixExperiment.md) for the exact input/output formula, transition table, and reproduction script. 

**Reproducibility:** compressed XZ/Base64 exact Lean source at the path above decompresses to 285 lines; SHA-256 of decompressed source `a035f6248194043509d47dd1aeee02c89374b37561db13897bb6b7d44f2e2cb4`. The manual `agent48-champion-root.yml` workflow decodes, hash-checks, imports unchanged `Frontier/Symmetry/RootShift/ChampionRootBridge`, source-checks `CountedSweep.lean` and `CountedOddBase.lean`, then compiles the quantified all-`c` theorem. [CI 42739466365 SUCCESS](https://github.com/FlareZ123/bb6/actions/runs/42739466365), `#print axioms counted_odd_counter` reports only `[propext, Classical.choice, Quot.sound]`. No `sorryAx` or independent machine-model premise. This is an intermediate contribution to the exact score critical path, and makes no claim about a complete BB(6) determination.

The independent [counted odd-decrement base certificate](CountedOddBase.lean) now proves the **48 successful TM63 primitive moves of the valuation-zero, zero-right-counter branch** in the actual physical semantics, allowing *arbitrary outside tape content*. In particular, start in source state D at head 0 with local marks exactly at positions 2, 3, 4, 7, 8, 9 within the closed interval [-1,12]; the other bits in that interval are zero. After exactly 48 successful transitions the state and head return to D/0, the original interval has additional marks at -1, 0, 10, 11, 12, and every exterior bit is unchanged. This is the source-connected first quantified case of the previously conjectural `C_Inc0_micro(z,c)=48+12*v₂(z)+12*c`: `v₂(z)=0`, `c=0`. Lean also proves a generic `run_frame` theorem protecting arbitrary context outside a finite read region, with exact finite-step simulation for the canonical section; every read head in the 48-step prefix is source-certified inside the 14-cell interval. [Full original-source CI 42737453470](https://github.com/FlareZ123/bb6/actions/runs/42737453470) passed, with only standard axioms and no `sorryAx`.

 The valuation-zero and one-trailing-zero local certificates **do not yet establish** the proposed all-parameter `Inc0` cost `48+12*v₂(z)+12*c`, nor a counted `Rst1'`/terminal theorem. The central missing work is to connect the legal published `S1`/`BinDec` words to an exhaustive counted sequence for an arbitrary trailing run of `d1` blocks, then compose the remaining fixed-length source steps and right-hand counter representation. The one-block theorem is evidence for the `12*v₂(z)` term, not a proof of its general coefficient.

## Original source and exact formulas

Compare the actual published [Rocq `TM63` source at pinned revision `3f302b87...`, `verify/SOBCv5.v` lines 10750–11283](https://github.com/ccz181078/busycoq/blob/3f302b87f5fb933c46e97672ffbb6907f373fb6e/verify/SOBCv5.v#L10750-L11283). The table is `1RB---_1LC0RF_1RE0LD_0LC1RB_1RA1RE_1RE0RD`. The original theorem `TM63.halt : halts tm c0` is an **existential halting proof**. See the separately source-verified [Agent48 champion-root six-step bridge](../agent48-champion-root/README.md) and [Agent42 two-cylinder coverage programme](../agent42-coverage-normal/README.md).

The published `Rst1'` macro is

```text
S1(L, 0, m1, a, 0, b)
  -->* S1(L+a+2, (4*2^L-1)*2^a-1, m2, b, 0, 2^b-1).
```

The new middle index is `R(L,a)=(4*2^L-1)*2^a-1`. `Rst1'_WF` establishes `R(L,a)<2^(L+a+2)`, so the next macro is applicable. `Rsts2H` proves halting when the `m2` index is congruent to 2 modulo 3. If it is congruent to 1, `Rsts1_v2` reaches another `m1` reset with the **same** length `L+a+2`.

## Complete three-case modular classification

The Lean file proves **for all natural** `k,a`:

```text
R(2k,   a)    % 3 = 2
R(2k+1, 2a)   % 3 = 0
R(2k+1, 2a+1) % 3 = 1
```

In the third case the next reset length `(2k+1)+2+(2a+1)=2(k+a+2)` is even. Consequently, composing the *already published* source lemmas gives the following mathematical sufficient halting region:

**Every physical `TM63.S1(L,0,m1,a,0,b)` halts whenever `L` is even or `a` is odd.** Even `L` terminates via one `Rst1'` and `Rsts2H`; odd `L` plus odd `a` takes `Rst1'`, `Rsts1_v2`, a second `Rst1'`, then `Rsts2H`. The parity-sector `L` odd and `a` even has residual index 0 modulo 3, so this argument makes **no claim** there. The Coq macro statements carry the necessary preconditions; this composition has not been added as a separately compiled Coq theorem.

The Lean `tower(0,b)=b`, `tower(n+1,b)=2^(tower(n,b))-1` and **corrected** `sumTower(0,b)=b`, `sumTower(n+1,b)=sumTower(n,b)+tower(n+1,b)` now match the original Rocq `t2` and `st2` literally. For any positive `b`, the Lean kernel establishes `sumTower(n,b)%2=(b+n)%2` without evaluating the astronomical tower. An initial draft incorrectly used `sumTower(0,b)=0` and asserted the generally false parity formula `n%2`; this was corrected on 2026-11-03 after re-reading source `st2`. The present genuine exponent uses `b=6`, so its parity and the subsequent halting residue conclusion are unchanged. Do not reuse the superseded general formula.

The authentic Rocq prefix `init` gives `S1(3,7,m2,6,0,63)`. `Rsts1` yields an `m1` configuration with `a=sumTower(7,6)+12`, which is odd. Lean theorem `published_blank_gate` establishes that the first reset has index 1 modulo 3 and the second reset has index 2 modulo 3 **for the enormous actual next exponent `tower(8,6)`**. This reconstructs the modular core of the existing Rocq proof without attempting to evaluate the giant number. It is a transparent check of previously established halting reasoning, not a novel champion decision.

## Verification and limits

Run `lean im-results/agent24-champion-time/ChampionModular.lean` under Lean **4.36.0-rc2**. Local run on 2026-11-03 was successful with `#print axioms published_blank_gate` returning `[propext, Quot.sound]` and no `sorryAx`. The theorem is **arithmetic about the published formulas**, with no local `TM63.S1` tape definition or imported Coq proof; only the original Rocq module supplies the machine-to-macro semantic link.

Crucially the original `TM63.halt` and the intermediate `-->*` statements give existence of finite paths, **without explicit counted primitive steps**. Neither this modular classification nor the Agent48 exact six-step root join provides a numerical theorem `HaltsAfter championTable N`. It would be unsound to treat the previously published approximate tower scale as a proved exact score. The global maximum proof also still lacks the universal six-state upper bound.

## Concrete next proof edge

The source-certified counted left and right sweep lemmas above can be used inside the actual physical-tape derivation. For an exact champion step score, strengthen the source macro chain `LC_Inc` / `Incs0` / `Rst2` / `Rst1` / `Rst0` / `Rst1'` / `Rsts1_v2` / `Rsts2H` to produce **primitive-step counts** alongside endpoint configurations. Compose these into an executable symbolic recurrence for the existing finite macro itinerary and check the start/root and final halting-query conventions against `BB6Coverage.HaltsAfter`. A source-certified finite numerical expression would supply an attainable lower bound, with global upper-bound completeness still separate. No such counted source proof is claimed here.

All novelty, source integration and universality claims remain deliberately qualified; this file is under `im-results/`.

## New primitive-step cost conjectures (finite evidence only)

The executable [`verify_counted_macros.py`](verify_counted_macros.py) uses the literal original 12 TM63 transition entries with a finitely supported bi-infinite tape. It interprets the original `TM63.S1` convention carefully: in Coq, `l <{{D}} r` places the head on **the last cell of the physical left word**, whereas the first cell of `r` is its right neighbor. Getting that offset wrong causes spurious failed macro matches. With the corrected convention, the raw blank-root simulator reaches the published `S1(3,7,m2,6,0,63)` **exactly after 27,959 ordinary transitions**.

Independent primitive-step simulation suggests three concise *all-parameter conjectures*. Let `v₂(n)` denote the number of trailing zero bits of positive `n`, and let `m=0,1,2` index the source's `Rst0/Rst1/Rst2` middle marker. For source transitions from `S1(L,n,m,a,0,b)`, with `1≤n<2^L`, to their exact published `S1` successor:

```text
C_increment(m,n,a,b) =
    6*4^b + 42*2^b - 9*b + 15 + 4*m + 12*(a + v₂(n))

C_reset_core(L,a,b) = 97 + 12*(L+a) + 3*b
C_reset_drain(b)    = 6*(4^b-1) + 42*(2^b-1) - 12*b
C_Rst1'(L,a,b)     = 12*(L+a) + 6*4^b + 42*2^b - 9*b + 49

C_Rst0'_to_halt_query(L,a,b) = 59 + 12*(L+a)
```

The `Rst1'` decomposition follows the **actual intermediate configuration** visible in its pinned Rocq proof: `S1(L+a+2,R(L,a),m2,b,2^b-1,0)`. The first formula's target is `S1(L,n-1,m',a+b+δ,0,2^b−1)`, where `m'` cycles 2→1→0→2 and `δ=1` for `m=0`, `δ=2` otherwise. The final formula counts successful transitions **up to**, and excluding, the undefined halting query. One must separately reconcile whether the external Busy Beaver scoring convention counts the terminal halt action.

All source-authentic endpoint configurations were compared by **complete finite set of marked cells relative to the head**, without fingerprints or approximate observations. Running the checked-in deterministic script locally on 2026-11-03 produced:

```text
INIT: 27,959 exact nonhalting blank-root moves to published S1
INC: 2860 finite original-step trials
RESET: 252 exact finite core/drain/composition trials
TERMINAL: 300 finite halt-query trials
ALL FINITE TESTS PASS; these do not establish quantified formulas.
```

The 2,860 increment checks cover all three markers, `L=1..6`, `1≤n<min(2^L,18)`, `a∈{0,1,3}`, `b=0..4`, and 160 pseudorandom extra instances with fixed seed `20261103`. The reset checks cover `L,a=0..5,b=0..6`; terminal checks `L,a=0..9,b∈{0,1,7}`. A separate exploratory experiment matched `Rst1'` for `b=0..11`, including a 25,251,790-step instance.

**Evidence class: finite computational conjecture.** Endpoint agreement for 3,412 instances is a substantial hint about a reusable exact raw-step cost model, but proves nothing for unrestricted `n,L,a,b`. The Lean file above certifies the source's modular gating arithmetic only. The proposed time formulas have **no universally quantified Lean or Coq proof**, no verified cross-language semantics transport, and supply **no certified numerical champion score**. Future research should first prove the 59+12(L+a) terminal and 97+12(L+a)+3b reset-core macros symbolically; then prove the v₂(n) carry-law and the geometric drain-cost recurrence. The latter has observed difference `C_drain(b+1)-C_drain(b)=18*4^b+42*2^b-12`, a natural induction target. Only then should costs be composed over the champion's massive macro itinerary.

## Formal closed form for the proposed binary drain and new micro-step test

A narrower raw-step experiment extracts the original `Inc0` decrement from a general `S1(L,n,m,a,z,c)` with `1 ≤ z < 2^a`. Its apparent primitive-step cost is
```text
C_Inc0_micro(z,c) = 48 + 12*v₂(z) + 12*c
```
and its exact endpoint is `S1(L,n,m,a,z-1,c+1)`, with unchanged physical left context. This was tested against all twelve real TM63 raw actions on **1,000 additional seeded random finite configurations** with varying `L,n,m,a,z,c`, and all tests matched. The extended [Python harness](verify_counted_macros.py) now exercises 4,412 finite instances across the complete set of macro families.

We also extracted the **fully proved arithmetic component** into [`CountPattern.lean`](CountPattern.lean). Its structural valuation word is
```text
carryPattern(0)   = []
carryPattern(b+1) = carryPattern(b) ++ [b] ++ carryPattern(b).
```
For `charge([v₁,...,v_N],0)=Σᵢ[48+12*vᵢ+12*(i-1)]` and `drainPattern(b)=charge(carryPattern(b),0)`, Lean 4.36.0-rc2 proves **universally**, without `sorry` or nonstandard axioms:
```text
carryPattern(b).length + 1 = 2^b
carryPattern(b).sum + b + 1 = 2^b
drainPattern(b) + 12*b + 48 = 6*4^b + 42*2^b.
```
The last theorem is `BB6ChampionArithmetic.drainPattern_closed`, checked by the actual Lean kernel; `#print axioms` reports only `[propext, Quot.sound]`. This explains the observed exponential drain *arithmetically* as the binary carry pattern accumulated by sequential decrements. Its proof is independent of any machine-level assumption. The previously compiled local templates cover the valuation-zero and one-trailing-zero cases with arbitrary right-counter length `c`. A new all-valuation original-table source candidate is described below, but until its exact import closure and transitive axiom audit pass, the all-parameter count remains unverified as TM runtime.

The next formalization target described in the earlier development has since been implemented as the uniform all-valuation H-run/S1 decrement and generic all-ones drain source chain in the section below. Its exact original-import compilation and transitive axiom audit remain pending; the symbolic `Inc0` and drain costs are not yet certified as a complete source-machine transition.

## Explicit symbolic score-consumption interface

The independent Lean4 [`CostRecurrence.lean`](CostRecurrence.lean) defines `sectionResult(n,m,a,b)`, the exact **published endpoint-update arithmetic** accompanied by the *conjectured* primitive-step cost `proposedIncrementCost` for each Rst0/1/2. The file proves for **all** `n,m,a,b` that the resulting marker is `(m+2n)%3`; in particular starting from m2, consuming `3k+1` macros ends at m1 and consuming `3k+2` ends at m0. These all-time arithmetic marker facts are Lean-kernel checked with `[propext, Quot.sound]` and no `sorryAx`.

The total definition `proposedTM63Moves` is an explicit huge natural-number expression for the TM63 A-root successful transitions: 27,959 prefix steps, 7 initial decrements, the first reset, a `resetIndex(3,a₁)`-length decrement stage, the second reset, a `resetIndex(L₂,a₂)`-length stage, and the terminal query setup. `proposedTM63Score=proposedTM63Moves+1` adds the halt query as required by the local `BB6Coverage.Attainable` convention.

**Root correction:** The historical champion A-root is the *E-root* of TM63 under state renaming. Agent48's original-source Lean theorem `champion_halts_offset` proves that its halting query occurs exactly six transitions **later** than the TM63 A-root's halting query. Therefore the symbolic candidate champion score is `proposedChampionScore=proposedTM63Moves+7`, representing those six extra successful transitions plus the one terminal halt query. This offset was explicitly corrected in the first draft of `CostRecurrence.lean`.

The `proposedChampionScore` expression is *intentionally unevaluated*: its nested iterates are astronomically large, and concrete numeral expansion is unnecessary for a source-connected proof of an expression-level exact score. It remains a **conditional candidate** because the uniform S1 decrement/drain chain and the remaining counted reset/prefix transitions do not yet have a passing original-import source closure, and the genuine blank-root itinerary is incomplete. Neither `CostRecurrence.lean` nor any current source candidate establishes `HaltsAfter championTable (proposedChampionScore - 1)`. That exact theorem is required before this expression can be used as an `Attainable` lower-bound witness.

## Source-recurrence consistency and conditional fuel theorem

Two additional Lean 4.36 files now expose a precise proof interface:

- [`StageAlgebra.lean`](StageAlgebra.lean) proves the exact arithmetic identity `authentic_first_stage_exponent : (sectionResult 7 2 6 63).exponent = sumTower 7 6+12`, as well as generic identities for the unchanged `t2/st2` recurrence and all-length endpoint exponents/right counters. This is a *symbolic proof*, so the huge exponent is never evaluated. Its axiom audits report only `[propext, Quot.sound]`; no `sorryAx`.
- [`FuelComposition.lean`](FuelComposition.lean) defines generic deterministic partial-machine fuel semantics and proves the universally quantified theorem `section_fuel_sound`: **if** every positive-index macro has the proposed exact cost and endpoint in the actual machine, then the entire arbitrary-length `sectionResult` stage executes in the sum of the proposed costs and reaches the exact reported full macro-configuration. The premise is a necessary, explicit assumption. Kernel check succeeded with standard axioms only. It does not assert the missing source macro-cost theorem for TM63.

[`CostRecurrence.lean`](CostRecurrence.lean) now imports `ChampionModular.lean` and additionally proves for the genuine astronomically large symbolic stage counts: `first_stage_exponent_odd`, `first_reset_index_one`, `middle_stage_marker_one`, `second_reset_index_two`, and `final_stage_marker_zero`. The final theorem uses the **actual symbolic second-stage right-counter and exponent**, rather than a dummy input. Thus the complete proposed macro **control flow** is mechanically aligned with the original Rocq halting argument, even though the primitive-step weights are still conjectural.

To check locally under the provided Lean 4.36.0-rc2, from this directory compile `ChampionModular.lean` to `ChampionModular.olean`, then `CostRecurrence.lean` to `CostRecurrence.olean`, then compile `StageAlgebra.lean` and `FuelComposition.lean` with this directory on `LEAN_PATH`. `CountPattern.lean` is standalone. All of these files were compiled successfully against the actual Lean 4.36.0-rc2 kernel on 2026-11-03, though **none are an original-source Cryptids/Rocq CI integration**, which is still an explicit future obligation.

The remaining decisive lower-bound obligations are now more sharply separated: compile and audit the uniform all-valuation S1 decrement/drain source candidate; prove the remaining authentic counted reset and root-prefix transitions in original TM63 tape semantics; and connect the resulting blank-root run to the terminal m0 halt query with the existing +6 root/+1 query convention. The source candidates below do not yet discharge those obligations. Proving the global maximum still requires a separate exhaustive coverage certificate.


## Uniform all-valuation S1 counted decrement (current proof candidate)

The primary original-table S1 counted-decrement path is now a single all-valuation construction; the earlier residue-specific positive-r prefixes and parity-complete composition are superseded for this purpose.

- `CountedCarryPrefixHRun.lean` proves `HOutputShape_leftOutput`, deriving the complete left-facing `carryLeftOutputBit` stream from the counted H-run shape. `carryPrefix_anyNonnegative_hRun` composes the exact H-run with the fixed 11-step B→E bridge, giving a `15+12*r` prefix for every `r≥0`, with six local output cells and preservation of the right exterior.
- `S1CarryInc0.lean` composes that prefix with the existing `33+12*b` suffix. The theorem `s1Config_counted_decrement_anyValuation_hRun` gives the canonical full S1 decrement `S1(z,b) → S1(z-1,b+1)` in `48+12*r+12*b` moves when `z=(2*q+1)*2^r`.
- `S1CountedInc0.lean` factors every positive bounded counter `z<2^a` in this form and proves the uniform cost `48+12*v₂(z)+12*b`. The older odd-canonical theorem remains available as regression evidence; it is not the primary all-valuation proof path.
- `S1CountedDrain.lean` instantiates the generic `CountedReset` recurrence. For an all-ones counter `2^k-1` and initial unary count zero, the candidate drain cost is `6*4^k+42*2^k-12*k-48`.

**Validation boundary.** The targeted original-import workflow run `43858822223` at old SHA `68280aa969d8a0741848fee7d79fcbd9db9ed151` failed in the H-run source with three boundary-expression mismatches and one malformed extraction of the run/shape conjunction. The current `CountedCarryPrefixHRun.lean` blob `a940aab604a76a87c8ac54106616cac4e2895d43` contains the corresponding repairs: normalized `-(3*r)` boundary expressions and separate `hExact.1` / `hExact.2` extraction. These are source repairs, not a successful compile. The existing manual `.github/workflows/agent42-counted-lbin-dec.yml` now rejects both `sorryAx` and `native_decide`. A focused local Lean preflight is still pending; do not dispatch the workflow until that preflight is clean.

The older `CountedCarryLeftOutputR23.lean`, `LongResidue1.lean`, and residue-specific branches remain in the repository as supporting/regression material for other reset compositions. They are no longer the primary S1 decrement path.

**Scope boundary: inner counter versus outer Rst prefix.** This S1 chain decrements the active inner S0 counter `z`. It does not prove the Coq `Rst0/Rst1/Rst2` prefix: that prefix starts with `z=0` and uses `LC_Inc` to decrement the *outer* binary counter `n` embedded in the left context. It needs a separate S1 source re-encoding of `binDec L n` (plus unary `a`) into the exact carry-input frame while preserving the right suffix `b`. The rho=3 local boundary trace also still needs the contiguous right-run and final three-cell zero boundary. See `im-results/agent42-carry-boundary/README.md` for the established local traces and remaining outer-prefix obligations.

This entire S1 chain remains an intermediate source candidate: it does not by itself establish the blank-root itinerary, a halt, an attained BB(6) lower bound, or an exact score.

## Marker-2 odd-n reset prefix: q4 decomposition (intermediate)

The q4 decomposition is the source-level route for the marker-2, odd-inner-counter Rst2 case. It now has a complete **proof candidate** from the original S1 input to the canonical next S1 state. The result remains in `im-results/` because the strengthened prefix, suffix, and endpoint modules have not passed the complete manual Lean audit.

**Prefix.** `im-results/agent6-q4-prefix/CountedQ4Prefix.lean` proves the original-table run for every odd `n < 2^L`, with cost `32+12*a`, the complete left-facing q4 word, and the finite right-shape contract. Its earlier finite-interface gate passed CI 43334058991 with no `sorryAx`. The current theorem additionally exports the complete right-facing stream, already established internally by the prefix proof; this strengthened signature has not yet been compiled.

**Suffix.** `im-results/agent8-counted-reset/Q4Suffix.lean` proves the proposed `39+3*b` frame decomposition: ten entry moves, a counted scan of `b` three-one blocks, and a 29-move local tail. Its source theorem is part of the current manual-only champion-root workflow, but no successful source-closure audit of the current revision is recorded.

**Full endpoint composition.** `im-results/agent24-champion-time/Q4RightEndpoint.lean` now contains the right and left infinite-stream endpoint lemmas, the source-run wrappers, `q4_suffix_run_target_of_prefix`, and `oddRst2_q4_counted_source`, plus the explicit root specialization `tm2_q4_root_source`. The generic theorem proposes the uniform theorem

```lean
run tm2 (71+12*a+3*b) (s1Config L n 2 a 0 b h) =
  some (s1Config L (n-1) 1 (a+b+2) (2^b-1) 0 (h+5+3*b))
```

for odd `n < 2^L`. The left proof separates the periodic `d0pow b` output, the six marked boundary cells, and the untouched q4-prefix left ray; the right proof uses the full prefix stream to establish the blank exterior. Together with the suffix frame's state/head, `config_ext` identifies the complete original-source target. All of these new declarations are **uncompiled proof candidates**.

For the authentic root `(L,n,m,a,z,b,h)=(3,7,2,6,0,63,29)`, the candidate is a 332-step transition to `s1Config 3 6 1 71 (2^63-1) 0 223`. Combined with the independently kernel-checked 27,959-step blank-root bridge, this would give a 28,291-step source prefix to that S1 state. Agent 48 has now replayed all 332 transitions with the exact 12-row table and compared the complete marked set against the canonical S1 encoder target; the symmetric difference is empty. The unbounded-coordinate reproducer/report are `im-results/agent48-counted-inc0/q4_root_endpoint_audit.py` and `Q4RootEndpointAudit.md`. This is exact reproducible computation, not a Lean proof of the transition. The encoder gives the same count and support: `binDec 71 (2^63-1) = d0pow 63 ++ d1pow 8` contributes 87 ones; `markerWord 1`, `d0`, `binDec 3 6 = d1 ++ d0 ++ d0`, and `lh` contribute 2+1+5+5, so the left stream has 100 ones. `s0RightFacing 0` contributes six more. The left stream length is 234, placing its far edge at `223-233=-10`, and the nine-cell right stream ends at 232. This is an independent consistency check, not a proof that the 332-step run reaches the canonical target.

The target has a positive all-ones S1 counter. Agent 48's `S1CountedDrain.s1Config_counted_drain_closed` applies at `(L,n,m,a,k,h)=(3,6,1,71,63,223)` and would take it to `s1Config 3 6 1 71 0 (2^63-1) 223` in `6*4^63+42*2^63-804` moves. Conditional on both q4 and the S1 decrement/drain chain compiling, the blank-root prefix through this drain would be `27959+332+(6*4^63+42*2^63-804) = 6*4^63+42*2^63+27487` steps. The `S1CountedInc0` and `S1CountedDrain` modules are uncompiled candidates, so this is not a certified lower bound or full halting score.

**Validation gate.** The current integration gate is the manual `.github/workflows/agent42-counted-lbin-dec.yml`, which stages the H-run, S1 decrement/drain, q4 endpoint, and M0-even 8q source chain. Its last attempt, run `43858822223` at old SHA `68280aa969d8a0741848fee7d79fcbd9db9ed151`, stopped in the H-run before reaching downstream modules. The current H-run blob `a940aab604a76a87c8ac54106616cac4e2895d43` repairs the reported boundary simplifications and run/shape extraction, but has not yet been compiled. The older Q4Suffix failure in run `43340804651` was patched by commit `8c10a5f05db5a5a0706395005f7fb7a7b3e24580`; that repair also remains unverified in the current full closure. The current workflow rejects both `sorryAx` and `native_decide`. Dispatch it once, only after the exact local source preflight is clean. Until the complete original-import closure passes, the q4-plus-drain root path remains conditional and is not a halt witness or BB(6) lower bound.

The finite q4 screens remain in [LCIncQ4Cut.md](LCIncQ4Cut.md) as empirical support, not a substitute for the quantified proof. No exact BB(6) score or universal six-state upper bound follows yet.


## 2026-11-13: generic q4 suffix endpoint and branch reuse

The q4 suffix endpoint has been generalized beyond the marker-2 odd-n branch:

- q4_suffix_left_word_general accepts an arbitrary source left word and a target identity of the form
  s1LeftFacing L n m a z = d0pow b ++ d1pow 2 ++ sourceLeft.drop 1.
- q4_suffix_frame_eq_s1Config identifies the complete suffix frame with a canonical S1 target when the prefix supplies that left stream, the q4 right-shape contract, and the blank right exterior.
- q4_suffix_run_to_s1Config packages the generic frame identity with the exact 39+3*b original-table suffix run.

These declarations are in Q4RightEndpoint.lean and have explicit #print axioms checks. The three earlier inline frame conversions were simplified to direct applications of q4_suffix_frame, since the local frame is definitionally the returned frame. None of the current Q4RightEndpoint revision has passed the full manual Lean workflow. Historical successful runs 43385544822 and 43385985633 predate the Q4 regression; run 43386376198 failed on an earlier revision and does not validate the present fixes.

**M=1,n=6 integration audit.** Agent 42 already has the canonical m=1,n=6 integration in im-results/agent42-champion-terminal/M1EvenQ4Suffix.lean and TM63M1EvenRootComposition.lean, including the counted drain and root composition. I briefly prototyped a separate M1EvenQ4Endpoint.lean using the generic interface, then found Agent 42's existing modules already cover the same stage. The duplicate prototype was deleted; it must not be added to CI. Agent 42's modules remain the canonical m=1,n=6 integration.

The generic endpoint remains useful as a branch-independent interface for the next reset branches. The next root-connected input after Agent 42's m=1,n=6 drain is the m=0,n=5 state with left parameter 2^63+72 and unary parameter 2^(2^63-1)-1. The unresolved work is the source-level reset prefix from this m=0,n=5 state, not another m=1,n=6 proof.

All statements above are intermediate proof candidates until the current Q4 source closure passes the manual Lean audit with no sorryAx. Keep them in im-results; they do not establish halting or the exact BB(6) value.


## m=0,n=5 odd reset prefix: proved source transition

M0OddQ4Bridges.lean and M0OddQ4Prefix.lean now formalize the m=0,n=5 branch for every a>0 and b≥0.

- The source prefix reaches the q4 cut in 24+12*a steps: a 9*a-step counted left sweep, a fixed 27-step finite bridge, and a 3*(a-1)-step right scan.
- The finite bridge is checked by decide from ⟨3,0,[-4,-1,2,3]⟩ to ⟨4,3,[2,1,-1,-4,-5,-6,3]⟩; the head trace is confined to [-6,3].
- The quantified cut-tape proofs establish the exact left-facing source word, right-facing q4 word, q4 shape, and blank right exterior.
- The generic q4 suffix endpoint then gives the exact reset target:
  s1Config 3 4 2 (a+b+1) (2^b-1) 0 (h+5+3*b).
- Total prefix cost: resetPrefixCost 0 5 a b = 63+12*a+3*b.

The main theorem is BB6Coverage.Agent24M0OddQ4Prefix.m0Odd_reset_prefix_to_s1. The targeted workflow .github/workflows/agent24-m0-odd-q4-prefix.yml compiled the complete dependency closure, both new modules, and their #print axioms checks under Lean 4.36.0-rc2. Runs 43402728285 and 43402788011 succeeded; the workflow rejects any sorryAx in the new modules. This also recompiled the repaired Q4RightEndpoint.lean, whose generic suffix endpoint theorems report only the standard propext, Classical.choice, and Quot.sound axioms.

This is a rigorous source-level reset-prefix transition, not a halting proof, a certified BB(6) score, or a universal upper bound. The next useful step is to instantiate it at the root-connected m=1,n=6 drain endpoint and establish the subsequent m=2,n=4 continuation; keep the result in im-results/ until integrated into a complete root-to-halt proof.


**Available next drain (source candidate).** The Agent 48 theorem candidate Agent48CountedInc0.s1Config_counted_drain_closed applies to this target without new decrement work, conditional on the current all-r S1 decrement/drain compile gate. At root parameters A=2^63+72, B=2^(2^63-1)-1, H=225+3*2^63, instantiate it with (L,n,m,a,k,h)=(3,4,2,A+B+1,B,H+5+3*B). Its bound follows from A>0:
2^B-1 < 2^B ≤ 2^(A+B+1).
It then transfers the unary counter to the right field, reaching s1Config 3 4 2 (A+B+1) 0 (2^B-1) (H+5+3*B) in 6*4^B+42*2^B-12*B-48 steps. This is a direct application of the generic source theorem, still conditional on the current all-r S1 decrement/drain compile gate, and not yet packaged as a new combined root theorem. The next unresolved stage is the m=2,n=4 reset/source continuation. Agent 42's candidates are `im-results/agent42-champion-terminal/M2EvenQ4Prefix.lean` and `TM63M0M2RootComposition.lean`: the 50-step finite bridge, `56+12*a` q4 prefix, and `95+12*a+3*b` full reset-prefix cost have been statically reviewed, but neither the module nor root composition has passed Lean compilation and transitive axiom audit. The last broader workflow run `43411782528` failed upstream in `M1EvenQ4Prefix.lean` before reaching M2, so it provides no validation for this stage.


**Root-specific instantiation.** M0OddQ4Prefix.lean now also defines m0OddRootA/B/Head mirroring Agent 42's tm63AfterM1EvenA/B/Head and proves m0Odd_root_reset_prefix from that exact root-connected S1(3,5,0,A,0,B,H) state. This root-specific application compiled in targeted CI run 43403557772 (commit 1a0f07b4b13d8107b0e513e941f982c3944580ff), with the no-sorryAx check passing. It still proves only the next source prefix, not the preceding root composition or a halting result.


## 2026-11-13: m=1,n=3 odd reset prefix (intermediate source candidate)

The root-connected state after the m=2,n=4 even increment is
`S1(3,3,1,A2,0,B2,H2)`. A new m=1,n=3 odd reset prefix has been derived for all
`a,b ≥ 0`:

```lean
run tm2 (67+12*a+3*b) (s1Config 3 3 1 a 0 b h) =
  some (s1Config 3 2 0 (a+b+2) (2^b-1) 0 (h+5+3*b))
```

The decomposition is:

- a counted left sweep of (3(3a+1)) moves;
- a 29-step finite bridge from
  `⟨3,0,[-7,-4,-1,2,3,4]⟩` to
  `⟨4,5,[4,3,2,1,-1,-4,-5,-6,-7]⟩`, with pre-step heads in ([-9,4]);
- an E-scan of (3a) moves;
- the q4 suffix after its four guard moves, (35+3b) moves.

Thus the total is (32+12a+35+3b=67+12a+3b=resetPrefixCost(1,3,a,b)).
The source left word uses `binDec 3 3 = d0 ++ d0 ++ d1`; the q4 cut's
left-facing stream is
`[true] ++ d1pow a ++ markerWord 0 ++ d0 ++ binDec 3 2 ++ lh`.
The new boundary-bit and tail lemmas align the finite bridge with that stream.
After the generic q4 endpoint, the all-ones counted drain gives the full
counted increment
`S1(3,3,1,a,0,b) -> S1(3,2,0,a+b+2,0,2^b-1)`.

Files:
- `M1OddQ4Prefix.lean`: parameterized q4-cut prefix, exact bridge, cut left/right stream and shape contracts, plus `m1Odd_q4_prefix_far_tail`, which proves the entire blank suffix from the original S1 right-facing encoding (the five-cell `q4RightShape` guard alone is insufficient for the suffix's infinite-tail premise).
- `M1OddQ4Suffix.lean`: generic q4 suffix endpoint plus counted drain.
- `TM63M1OddRootComposition.lean`: extends the blank-root chain through the four increments
  ((1,6)), ((0,5)), ((2,4)), and ((1,3)), with the residual itinerary now beginning at
  `sectionResult 2 0`.
- `m1_odd_q4_replay.py`: independent literal-table replay. It checks 81 full-tape cases
  (0≤a,b≤8) and 36 q4-cut left/right-shape cases (0≤a,b≤5); all matched exactly.

Agent 42 also supplied a compact 26-step bridge on ([-6,1]). The 29-step bridge used
here is the same deterministic path with the following three state-4-on-one moves
absorbed into the finite frame; both decompositions have the same (32+12a)
prefix cost. The new prefix, suffix, and root-composition modules plus the replay
script have been added to the existing manual-only
`.github/workflows/agent42-champion-terminal-source.yml`; no push/PR trigger was
added. **No CI run has yet compiled these three new Lean modules.** They remain
intermediate proof candidates, not certified results. The next mathematical
source stage is `S1(3,2,0,...)`, i.e. marker (m=0,n=2), followed by
(m=2,n=1). No exact BB(6) value or universal upper bound follows yet.


## 2026-11-13: m=0,n=2 even reset prefix and counted increment (intermediate)

The next source state after the m=1,n=3 odd stage is
`S1(3,2,0,a,0,b,h)`. A new parameterized q4 route has been derived for
all (a>0,b\ge0):

- After the (3a)-cell counted left sweep (9a primitive moves), the
  fixed 39-step bridge is
  `⟨3,0,[-7,-6,-5,-4,-1,2,3]⟩ -> ⟨4,3,[2,1,-1,-4,-7,-8,-9,3]⟩`,
  with its read-head trace confined to the local frame ([-9,2]).
- An E-scan of (3(a-1)) cells reaches state 4 at the original head.
  The q4 cut is therefore reached after (36+12a) moves.
- Its left-facing word is
  `[true] ++ d1pow (a-1) ++ markerWord 2 ++ d0 ++ binDec 3 1 ++ lh`,
  and the right side satisfies the generic `q4RightShape` for b.
- The generic q4 suffix contributes (39+3b) more moves, so the exact
  reset-prefix cost is
  (75+12a+3b=resetPrefixCost(0,2,a,b)), ending at
  `S1(3,1,2,a+b+1,2^b-1,0,h+5+3*b)`.
- The existing exact counted drain then yields the complete counted
  increment to `S1(3,1,2,a+b+1,0,2^b-1,h+5+3*b)`. Its closed drain
  cost is (6\cdot4^b+42\cdot2^b-12b-48), so the full increment cost
  is `proposedIncrementCost 0 2 a b`.

The new source modules are:

- `M0EvenQ4Bridge.lean`: exact finite bridge, head confinement, and
  the parameterized post-sweep input-frame match.
- `M0EvenQ4Prefix.lean`: counted sweep/bridge/scan composition, q4
  right-shape and complete left-facing stream, suffix-left identity,
  `resetPrefixCost 0 2` arithmetic, and `m0Even_q4_prefix_far_tail`,
  which proves the entire blank suffix from the original S1 right-facing
  encoding rather than extrapolating the five-cell q4 guard.
- `M0EvenQ4Suffix.lean`: generic q4 endpoint plus the counted drain, now
  consuming the full-tail theorem.
- `m0_even_n2_replay.py`: independent literal-table replay.

The replay passed 48 bridge-decomposition, q4-cut, and full reset-prefix
cases ((1\le a\le8,0\le b\le5)), plus 25 complete counted-increment
cases ((1\le a\le5,0\le b\le4)). It compares complete finite
marked-cell sets, not fingerprints. These are reproducible computational
checks, not quantified proofs.

A separate targeted workflow,
`.github/workflows/agent24-m0-even-q4-prefix.yml`, stages the exact
dependencies, runs the replay, and compiles only the finite bridge and
prefix. The existing manual-only champion workflow was restored to its
prior ownership boundaries after coordination: Agent 42 owns integration
of this new source theorem into the shared root composition. The exported
source theorem `m0Even_q4_counted_increment_source_symbolic` is ready to
consume from the preceding m=1,n=3 endpoint. The successor state is
`S1(3,1,2,a+b+1,0,2^b-1,h+5+3b)`; its residual itinerary next uses the
((2,1)) reset. The new M0-even Lean modules remain proof candidates until
the targeted CI compile and the shared root integration complete. No exact
BB(6) value or universal upper bound is claimed.
