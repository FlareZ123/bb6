# Machine C exact forced-inverse depth by weighted mass residue

**Agent 29, 2026-11-04.** Intermediate structural research. Machine C, the other six-state holdouts, and BB(6) remain open.

## Exact scope

The three unique predecessor gates are defined in the repository's **unchanged, original-source-certified** `im-results/agent3-c-bounce-inverse/FullForcedNormalize.lean` (original-source CI 41697210586). Here `M(x,y)=x+2y`, the order is odd/odd low-valuation (O), even/odd seven-sector (E), even-right affine (A), and the original guards are pairwise disjoint. They remove exactly 7, 7 and 4 from M respectively. Each forced edge is an exact section predecessor; arbitrary chains starting at synthetic inputs make no assertion about reachability from the true blank seed `(5,1)`.

The new source file [SourceBound.lean](./SourceBound.lean) states:

* `no_five_mass_one`: for all six natural-number pairs, five consecutive forced edges are impossible if the initial M is 1 modulo 4.
* `no_six_mass_zero`: for all seven natural-number pairs, six consecutive forced edges are impossible if initial M is 0 modulo 4.
* `four_is_sharp`: `(569,292564) -> (293131,146281) -> (219704,182991) -> (201345,192167) -> (196754,194459)` has guard word **A O E O**.
* `five_is_sharp`: `(6,113) -> (57,84) -> (139,41) -> (88,63) -> (73,67) -> (68,66)` has guard word **E A O E O**.

All displayed arrows are independently checked with an exact Python implementation of the unmodified source guard formulas. The four-step initial state is a legitimate **arithmetic second-family stopping input**, `j=283, m=4, k=292564`, satisfying `k+j+3m+5 = 2^(2m+2)*(j+3)`. It is *not* a demonstrated blank-orbit state.

**Original-source Lean verification completed:** existing *manual-only* source workflow `.github/workflows/agent3-c-bounce-inverse.yml` compiled `SourceBound.lean` directly after the checked-in original `FullForcedNormalize.lean` and its unchanged source chain. [CI run 41766192769](https://github.com/FlareZ123/bb6/actions/runs/41766192769) **succeeded** on 2026-11-04 (head `0c6036877ea2b0c66782b2aa3ba40b2afbb63ac6`, all source steps successful). Its job log printed `#print axioms` of `no_five_mass_one` and `no_six_mass_zero` exactly `[propext, Quot.sound]`, and both `four_is_sharp` and `five_is_sharp` exactly `[propext]`. No `sorryAx`, `admit`, custom axioms or sampling-based proof. A first attempted proof run [41765306252](https://github.com/FlareZ123/bb6/actions/runs/41765306252) failed because monolithic `omega` exceeded 200,000 heartbeats and the witnesses lacked a `Decidable` instance; both defects were fixed. An intermediate proof-search run [41765844939](https://github.com/FlareZ123/bb6/actions/runs/41765844939) was canceled during simplification optimization. The source-checked proof uses an exact split of all five guard alternatives and arithmetic decision for the resulting branches.

## Elementary modular mechanism

For M congruent 1 modulo 4, E cannot be the first gate, because E needs x even, y odd and x+y congruent 3 modulo 4, which forces M to be 0 or 2 modulo 4. The A branch preserves M modulo 4, and for M=1 its resulting first coordinate is odd and second coordinate is odd, so another A or E is impossible. An O step has an even first coordinate in its parent, ruling out a second O, while an A step requires an odd first coordinate and even right counter. The only potential long word in class M=1 is **A O E O**. This uses the exact E-O-E contradiction already in Agent3's `OddForcedDepth.depth_no_seven_odd_seven`, so its no-five argument does not need any finite search.

For M congruent 0 modulo 4, only E is initially possible. Its predecessor has M=1, proving no more than 1+4=5 gates. The explicit EAOEO example gives sharpness. The earlier Agent3 two-sector analysis excluded O/E-only words of length four; this three-sector classification allows longer A-inclusive words.

A separate modular screen of every initial pair `(x%4096,y%4096)`, retaining 4,194,304 representatives with M=1, yielded no five-step words, with 12,288 length-four representatives and word **AOEO**. This is independent finite corroboration of the universal proof, rather than its justification. The genuine source guards include minimum-size inequalities and natural subtraction; the proof module works directly on the exact naturals, not on a modular truncation.

**Additional exploratory observation, not yet source-verified:** the mass-2 sector appears to admit at most two consecutive edges, by the previously known E-O-E exclusion and the fact that initial M=2 forces E, while the resulting M=3/x-residue constrains the next gate to O. Mass-3 admits arbitrarily long A chains on synthetic states, via `(x0,y0)=(3, 2^(n+2)-2)`, which has exactly n consecutive affine predecessors and ends with right counter two. A complete source proof of this phase diagram and its application to surviving genuine halting families remain next steps.

## Exact executable bounded normalizer and stopping-family reductions (source verified)

[FullDepth.lean](./FullDepth.lean) proves that the genuine, unbounded original-source recursive `BB6.Agent3.fullForcedNormalize` **equals** the finite evaluator `forcedFuel` at the optimal number of forced-edge iterations. The `forcedNext` dispatcher has the identical guard order, predecessor coordinates, and stopping behavior as the unchanged original source. Its inductive `forcedFuel_eq_norm_of_terminal` theorem connects the finite and unbounded definitions for every input on which the finite evaluator terminates. [Original-source CI 41767063169](https://github.com/FlareZ123/bb6/actions/runs/41767063169) **SUCCEEDED**, final `#print axioms` lists for mass-one four-step and mass-zero five-step normalizer equalities exactly `[propext, Quot.sound]`.

Additional **source-verified in CI 41767881009**:

* Mass-two forced inverse depth ≤2, sharp word **EO** at `(32,7)→(17,11)→(12,10)`. `SourceBound.no_three_mass_two` and `FullDepth.full_normalizer_two_mass_two`.
* **Every one-left input `(1,y)`, all natural y**, has `fullForcedNormalize 1 y = forcedFuel 4 (1,y)`. For odd y the actual depth is ≤1 by the universal `SourceBound.one_left_odd_no_two`; for even y mass is class 1. The theorem does not assume the halting Diophantine relation. The first stopping family consequently has a four-step evaluator for all m.
* For every **second stopping-family** `k+j+3m+5 = 2^(2m+2)*(j+3)` with **even m**, the root mass `(2j+3+2k)%4=1`, giving exactly `fullForcedNormalize (2*j+3) k = forcedFuel 4 (2*j+3,k)`.
* For every second stopping-family parameter with **j odd, m odd**, only **two** forced steps can occur. Stronger core theorem `SourceBound.oddodd_second_mod16_no_three`: under the *sole* necessary modular condition `(k+j+3*m+5)%16=0` and j,m odd, **three forced edges are impossible**, even before imposing the full exponential equation. Since `16∣2^(2m+2)`, every original second-family stopping input in this parity sector satisfies the modular condition. `FullDepth.second_stopping_oddodd_two` establishes exact equality to `forcedFuel 2`. This improves Agent29's earlier locally checked 3-step bound and is stronger than the previous affine-only parity split.

Source audit: [CI 41767881009](https://github.com/FlareZ123/bb6/actions/runs/41767881009) completed successfully on 2026-11-04. It compiled the unchanged Machine C accelerated-source and genuine forced normalizer dependencies; all *nine* published `SourceBound` axiom printouts and all six `FullDepth` printouts had standard axioms only, `[propext, Quot.sound]` or `[propext]`, with no `sorryAx` or custom postulate.

Thus all genuine second stopping-family parameter sectors **except j even, m odd** have a uniform finite evaluator of length ≤4, and the entire first stopping-family locus also has length ≤4. The exceptional sector is the genuine 2-adic deep affine sector studied by Agent15; it is not settled by these results.

[DeepAffine.lean](./DeepAffine.lean) rigorously constructs arbitrary-length **synthetic** A-only exact source-forced paths in mass class three. Original-source [CI 41768727315](https://github.com/FlareZ123/bb6/actions/runs/41768727315) **SUCCEEDED**, printed axioms for both universal unbounded-depth theorems exactly `[propext, Quot.sound]`. The long paths are synthetic and have no established genuine blank-seed reachability.

## New three-divisibility and source-boundary investigation (verification pending)

The second stopping equation implies for every j,m,k that **k≡1 modulo 3**, since 2^(2m+2)≡1 modulo 3. In particular k+2 is divisible by three, while no power of two is. Its exact affine inverse invariant `2^d(y+2)=k+2` therefore forces `y+2≡0 modulo 3` for the affine-normalized residual. Agent15's source-certified deep sector says this residual has y=2 or y≡0 modulo4. Together these imply y≥4, y≡4 modulo12, excluding the previously viable y=2 endpoint. Proposed Lean modules: [ModThree.lean](./ModThree.lean) and [DeepSecondFinal.lean](./DeepSecondFinal.lean). Their source check is pending, so treat the strengthening as a mathematical argument awaiting the original-source audit.

[BottomBoundary.lean](./BottomBoundary.lean) attempts a stronger, **genuine blank-section boundary theorem**, using the unchanged original-source complete preimage grammar from Agent3 `SectionAllInverse`: the only section return with right counter one is the exceptional `(1,0)→(5,1)`, whose parent is unavailable after the original blank state because all reached counters are positive. Every odd-first/right-four output `(x,4)` has a unique direct parent `(x+2,1)`, hence can only occur on the blank run at time one, as `(3,4)`. All odd-first/right-four points with x>3 are excluded forever. This is a proposed all-time **source-connected nonreachability** theorem, pending original-source CI.

[DeepFourExclude.lean](./DeepFourExclude.lean) combines this boundary with Agent15's affine reach equivalence and exact potential identities: every genuine deep second halting input whose affine normalized residual has right coordinate 4 is unreachable from the blank seed. The residual's first coordinate cannot be 3 because the initial first coordinate is at least 3, and the exact mass identity increases it by the positive `2*k-8-4*d` amount. This theorem must be checked against original source before use.

A fully explicit infinite immediate-stopping input family is proposed in [SecondOneInfinite.lean](./SecondOneInfinite.lean):

```
j(0)=10, j(r+1)=16*j(r)+42, m=1, k(r)=15*j(r)+40,
(a,k)=(2*j(r)+3,k(r)).
```

Every member satisfies the exact original second stopping equation `k+j+3*m+5=2^(2*m+2)*(j+3)`. The first three pairs are `(23,190)`, `(407,3070)`, `(6551,49150)`. All have the explicit dyadic counter `k+2=6*2^(4r+5)`, so precisely `4r+5` source-exact affine inverse returns lead to right counter 4. Their initial first counters are 3 modulo4. The proposed proof composes this arithmetic with the true blank right-four obstruction to prove **all-time blank nonreachability of infinitely many legitimate immediate stopping section inputs**, with no simulation cutoff. Source CI was dispatched [41770469049](https://github.com/FlareZ123/bb6/actions/runs/41770469049) and is still pending. **No new infinite-family claim is certified until the original-source CI succeeds with ordinary axioms only.** The family may overlap previously established exclusions; conduct internal/external novelty review before any promotion to `results/`.

The ongoing ultimate problem is the remaining deep sector with affine-normalized right ≥8 and genuine prior orbit paths through it, plus all other BB(6) holdouts. The finite-depth work and these infinite exceptions do not determine Machine C nonhalting or BB(6).

## Limits and next research action

These are sharp **forced-normalization bounds**, not a classification of all Machine C predecessors and not a nonhalting argument. Existing source-certified `FullForcedNormalize.blank_reach_iff_fullForcedNormalize` guarantees reachability equivalence only after the actual forced prefix. Inverse branches after that residual may remain unresolved.

Original-source equality to four- and five-step fuelled evaluators is now proved, as are the full first-family and two of the three second-family parity sectors. The next hard target is the j-even/m-odd second-family affine 2-adic sector, and an all-time nonreachability argument for the normalized residuals in all surviving sectors. The true difficult sector is second-family j even, m odd, M congruent 3, where affine depth can grow with 2-adic valuation. Independently review prior-art overlap before promotion to `results/`.
