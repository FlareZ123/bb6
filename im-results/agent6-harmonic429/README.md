# Agent 6: BB(6) #429 harmonic-gate and corridor transfer programme

## 2026-11-04 13:55 UTC: stronger rooted #429 inverse-halting barriers (Agent 6)

**Exact theorem scope.** The genuinely blank-origin accelerated trajectory from `(0,0)`, with `BB429.next` as in unchanged `agent5-429-rank/BB429Rank.lean`, cannot encounter a terminal junction `b+1=2*a` with `a%64=41`, `a%64=49`, or **`a%64=21`**. The first two cases are in [BB429NewGate.lean](BB429NewGate.lean); the entire 21 sector, including its exceptional first value `a=21`, is in [BB429TwentyOne.lean](BB429TwentyOne.lean). The separate [BB429Deep17.lean](BB429Deep17.lean) proves every actual terminal with `a%32=17` must have `a%128=81`. This refines the original four-class modulus-32 criterion to a **six-residue modulo-128 necessary condition**:

```
a%64=9 OR a%128=81 OR a%64=53 OR a%128=125
```

This filter represents **2+1+2+1=6 residues modulo128**, namely {9,73,81,53,117,125}. It is a restriction on *possible halting accelerated states of this one rooted machine*, not a new six-state Busy Beaver bound or a decision of #429. The 29 sector includes all sufficiently long first-branch burst endpoints and remains open.

**Proof mechanism.** The terminal incoming transition is always the first (doubling/subtraction) branch, so predecessor coordinates are exactly `(x,6*x+8)`, with terminal counter `a=2*x+3`. The 41 and 49 modulo64 exclusion files exhaust every affine predecessor branch and force eventual contradiction with the prior genuine blank-orbit invariant: positive even first counter implies second counter 2 modulo4. For the 21-mod64 family, a four-stage inverse chain passes through `(16*k+9,96*k+62)`, `(8*k+3,112*k+71)`, `(4*k,120*k+74)`, `(34*k+15,60*k+37)`, then its forced predecessor `(17*k+6,94*k+52)`. When `k≥2` is even, this final predecessor has positive even first counter and second counter divisible by four. An alternative immediate parent `(40*k+18,48*k+33)` is also forbidden by the same parity invariant. The exceptional `k=0` root is disposed of by direct 12-step kernel reduction and the monotone rank `2*u+w`: at step12 the genuine orbit is `(11,62)` of rank84, so it can never subsequently reach `(0,74)` of rank74. The 17-sector deeper exclusion uses additional disjoint complete affine predecessor branches and has an exact all-natural statement.

**Two new full-residue inverse barriers.** [BB429NoTwentyNine128.lean](BB429NoTwentyNine128.lean) excludes terminal a%128=29 through the complete affine inverse chain to (4q-2,504q+104), which violates the positive-even parity invariant for all q>0; q=0 has no predecessor at an intermediate state. [BB429NoNinetyThree128.lean](BB429NoNinetyThree128.lean) excludes terminal a%128=93 via the complete affine inverse chain to (4q,504q+356), which violates the parity invariant for q>0. Its q=0 exception (0,356) is excluded by a kernel-checked 63-step root prefix and monotone rank: run63=(93,173) has rank359>356. Both were checked locally with Lean4.36.0-rc2 and standard axiom audit; original-pinned-source verification is separately tracked. [BB429InverseParity.lean](BB429InverseParity.lean) generalizes the exact two-parent halting-feeder inverse grammar and parity obstruction for non-first one-step candidate seeds.

**The last 29-sector residue barrier.** [BB429NoSixtyOne128.lean](BB429NoSixtyOne128.lean) excludes every terminal a%128=61 through a full inverse predecessor chain ending at (4q-1,504q+230). Generic q>0 predecessors lead to forbidden positive even/odd w or zero-first/odd w configurations. The exceptional q=3 first-counter-11 branch is handled by a finite 351-step kernel-checked prefix: at n=351 the real root trajectory is (21,1723), rank1765, above the exceptional target (11,1742) rank1764. Standalone local Lean4.36 checked the entire module with the standard logical axioms only. The pinned original-source audit is run [41847807220](https://github.com/FlareZ123/bb6/actions/runs/41847807220). This leaves the **sole** possible first-counter residue among the original 29 modulo32 sector as 125 modulo128, including the difficult long first-only burst family.

**Evidence and provenance.** Local Lean **4.36.0-rc2** compiled all three new arithmetic files in the precise imported dependency order with `#print axioms` limited to `propext`, `Classical.choice`, and `Quot.sound`. The matching local `BB429Rank` and `BB429NoThree` input definitions were checked against the source text; locally copying a definition alone does not constitute unchanged-original-source verification. The [first full original-source manual CI 41839354284](https://github.com/FlareZ123/bb6/actions/runs/41839354284) **succeeded for `BB429NewGate`**, both unchanged pinned DeepMind Cryptids accelerator and standalone proof. Subsequent runs aim to compile `BB429Deep17`, `BB429TwentyOne`, and [SourceRawHaltRefined.lean](SourceRawHaltRefined.lean) directly against the original source. [Run 41841143365](https://github.com/FlareZ123/bb6/actions/runs/41841143365) failed during the upstream Mathlib cache extraction with **disk quota exceeded**, before any of the new Lean proof sources were compiled in the original-source job; this is infrastructure failure, not a refutation. The current manual source workflow includes the stronger theorem. Run [41845915852](https://github.com/FlareZ123/bb6/actions/runs/41845915852) fully succeeded for `BB429NoTwentyNine128`, `BB429NoNinetyThree128`, and the seven-lift source-root equivalence. The six-lift source-root equivalence and last `BB429NoSixtyOne128` module are scheduled in run [41847807220](https://github.com/FlareZ123/bb6/actions/runs/41847807220); check that run before claiming original-source verification.

**Remaining question.** The refined condition still leaves infinitely many terminals. A priority is a genuinely root-specific obstruction for the 29 modulo32 long-burst family, an elimination of one complete residual sector, or a blank-root halt witness. A deeper finite quotient without new all-time logical implications has limited value. External novelty relative to ongoing BB6 research has not been established.


## 2026-11-04: two new all-time halting-sector exclusions (Agent 6 follow-up)

**Mathematical statement (latest):** For the genuine blank-root orbit of the exact #429 high-level map, a halted state cannot have first counter congruent to **3 modulo 4** or **25 modulo 32**. Combining these with the prior six-class theorem reduces the necessary halting classes from `{3,9,17,21,25,29}` to **`{9,17,21,29}` modulo 32**. The four classes remain possible in the logical reduction, with no reachability witness or global machine decision.

- [BB429NoThree.lean](BB429NoThree.lean): Every positive even first counter reached by a successful macro step has second counter 2 modulo 4. An incoming step to a halting state with first counter 3 modulo 4 must have predecessor `(x,6*x+8)` with even `x`. Positive `x` violates the preceding parity restriction; `x=0` gives `(0,8)`, excluded for all time because the genuine root goes immediately to `(0,12)` and every later successful step strictly increases `2u+w`. This excludes the full first-counter 3 modulo 4 class (and, in particular, the previously surviving 3 modulo 32 class).
- [BB429NoTwentyFive.lean](BB429NoTwentyFive.lean): An incoming step to a halt with first counter 25 modulo 32 forces its predecessor into the complete affine family `(16k+11,96k+74)`. For positive k, all predecessors are either `(8k+4,112k+85)` (forbidden positive-even first counter with odd second counter) or `(40k+23,48k+39)`. The latter requires predecessor `(20k+10,88k+62)`, which itself requires `(42k+22,44k+31)`, again contradicting the parity restriction. The exceptional k=0 state `(11,74)` is excluded by an exact 15-step finite-prefix certificate and rank growth (`run 15 (0,0)=(23,51)`, rank 97 vs target rank 96). Thus an entire infinite class is excluded, not merely finitely many examples.
- [SourceRawHaltFive.lean](SourceRawHaltFive.lean) and [SourceRawHaltFour.lean](SourceRawHaltFour.lean) transport these arithmetic restrictions through the unchanged pinned Cryptids source accelerator and prove **exact equivalences** between genuine raw-machine halting and hitting one of the surviving terminal classes. These are halting-gate **reductions**, not decisions.
- **Verification:** Manual original-source CI [41774475845](https://github.com/FlareZ123/bb6/actions/runs/41774475845) successfully compiled the unchanged original pinned Cryptids accelerator and `SourceRawHaltFive.lean`, and standalone Lean4.36.0-rc2 completed. Standalone all-module Lean CI [41775212673](https://github.com/FlareZ123/bb6/actions/runs/41775212673) also succeeded for `BB429NoTwentyFive.lean`. Original Cryptids CI for `SourceRawHaltFour.lean` was separately dispatched; do not claim that source-level verification is complete until its run succeeds. All checked principal Lean axiom audits show only standard axioms (no `sorryAx`).
- The new exact inverse family is distinct from the earlier modulo-only six-class sieve; external novelty has not yet been independently checked. These intermediate results do not determine BB(6) or settle machine #429.

## 2026-11-04: six-class all-time halt sieve, original-source CI certified

**Main mathematical theorem:** Given any number of accelerated applications from the actual blank-root high-level start `J(0,0)`, if the next accelerated action halts, its first counter satisfies

```
u mod 32 ∈ {3, 9, 17, 21, 25, 29}.
```

This excludes the other **26 of 32** congruence classes of potential halting states for this rooted machine. The six remaining classes are necessary possibilities, **not** six demonstrated halts. The theorem has no finite-time bound, yet the machine's behavior and the exact value of BB(6) remain undecided.

[BB429Mod32Six.lean](BB429Mod32Six.lean) is the arithmetic statement, relying on four independently Lean-kernel checked certificates:
- [BB429Mod8.lean](BB429Mod8.lean) proves a global 17/32-cell congruence invariant for the exact high-level map, containing `(0,0)`.
- [BB429Extra11.lean](BB429Extra11.lean) and [BB429Extra19.lean](BB429Extra19.lean) exclude the `11 mod 16` and `19 mod 32` halting classes through one- and two-stage forward restrictions.
- [BB429OneGate.lean](BB429OneGate.lean) and [BB429Thirteen.lean](BB429Thirteen.lean) exclude halting classes `u mod 32 = 1,13`: a terminal residue has two modular predecessors, each of which is impossible after even one valid step from the base invariant.
- [BB429Depth4.lean](BB429Depth4.lean) excludes `u mod 32 = 5` by a four-level backward barrier. Its forbidden sets modulo `(32,64)` are

  ```text
  B1 = {(6,62),(22,30),(14,46),(30,14),
        (2,6),(18,38),(10,54),(26,22)}
  B2 = {(15,47),(31,15),(7,63),(23,31)}
  B3 = {(1,14),(17,46)}
  B4 = {(5,9)}
  ```

  For every actual accelerated transition, the Lean proofs establish that a predecessor satisfying the base invariant cannot enter `B1`, and cannot enter `B(i+1)` when it avoids `B(i)`. Since `(0,0)` avoids all levels, no blank-root accelerated state enters `B4`. The genuine halt line `w+1=2u` would force `w mod 64=9` if `u mod 32=5`, giving a contradiction.

**Original-source verification:** Native manual [CI run 41769322879](https://github.com/FlareZ123/bb6/actions/runs/41769322879) passed both jobs, including successful original unmodified Cryptids `highLevelNext` and raw-TM accelerator under pinned original revision `c86f15861709b76042998c5211c7b2f83991621b`, all unchanged arithmetic proofs, and [SourceMod32Six.lean](SourceMod32Six.lean) establishing the same six-class necessary halt gate in the original published high-level source. The older preliminary nine-class check passed separately in [CI 41768202920](https://github.com/FlareZ123/bb6/actions/runs/41768202920). All principal `#print axioms` checks show only standard Lean foundational axioms, no `sorryAx`.

[SourceRawHaltFunnel.lean](SourceRawHaltFunnel.lean) is now **native-source certified** in [CI run 41771004542](https://github.com/FlareZ123/bb6/actions/runs/41771004542): it proves the direct raw-machine implication `IsHalt target → ∃ n,u,w,` genuine source halts at `J(u,w)` with `u mod 32` in the six classes. It uses the original pinned Cryptids theorem `IsHalt target ↔ CollatzHalts highLevelNext highLevelStart`, a proved equality of iterated source semantics, and a last-successful-state lemma. The #print axioms check reports only ordinary Lean foundations. [SourceRawHaltIff.lean](SourceRawHaltIff.lean) now proves the **exact equivalence** `IsHalt target ↔ ∃ n,u,w, actual source blank orbit reaches a high-level halting junction with u%32∈{3,9,17,21,25,29}`. Manual [CI run 41771433374](https://github.com/FlareZ123/bb6/actions/runs/41771433374) succeeded in both the original pinned Cryptids source job and standalone Lean job. This is a genuine exact *reduction* to six infinite families, **not** a decision of their reachability or of BB(6).

[abstract_sieve.py](abstract_sieve.py) reproduces a conservative finite modular quotient exploration. For modulus 32 it sees 488 of 2,048 possible residue pairs and six halting-line residues `{3,9,17,21,25,29}`. Because this intentionally overapproximates the branch guards, these are computational observations; the Lean proof above is independent of its soundness.

**Arbitrary-power first-burst limitation.** [BB429PowerBarrier.lean](BB429PowerBarrier.lean) and [BB429PowerBarrierBurst.lean](BB429PowerBarrierBurst.lean), compiled successfully with Agent 5's unchanged original `BB429Burst.lean` in standalone [CI 41770902578](https://github.com/FlareZ123/bb6/actions/runs/41770902578), prove for every natural `k≤n` that an exact first-branch prefix of length `n`, ending at first counter `a`, satisfies `(a+3) mod 2^k=0`. In particular `n≥5 ⇒ a%32=29`. The surviving 29 class is therefore inherent to long first-branch bursts, explaining why simply extending first-counter modulus sieves may not eliminate the genuine halting hazard. This statement is an elementary consequence of Agent 5's previously verified exponential prefix formula and does not claim independent breakthrough novelty.

**Eleven-reset post-turnaround candidate.** [BB429ElevenSeed.lean](BB429ElevenSeed.lean) derives under the exact non-first-transition guard `w<2u+3` that every transition entering `(11,v)` has `v%4=2`. Combining Agent 5's exact gateway formula, any subsequent first-only burst ending in a halt must have length `n%4=1`. Both universal lemmas passed [standalone Lean CI 41771997214](https://github.com/FlareZ123/bb6/actions/runs/41771997214) with the exact Agent 5 arithmetic map and first-burst formula. They restrict one reset family and do not decide any actual blank-root halt.

**Significance boundary:** The exact published Cryptids acceleration and its raw-TM correctness are prior work. The new contribution here is the machine-specific all-time modular pruning and its simple backward proof certificates. Independent priority against the wider mathematical literature has not been established. These remain intermediate results in `im-results/`, with the full BB(6) problem open.

## 2026-11-04: original-source verification repaired, new infinite modular gates

**Native pinned source verification is now successful:** manual [CI 41765557427](https://github.com/FlareZ123/bb6/actions/runs/41765557427), source job 126362985268, built the unchanged original DeepMind Cryptids `c86f15861709b76042998c5211c7b2f83991621b` accelerator under pinned Lean 4.35.0-rc4, then compiled the original checked-in Agent5/Agent6 local module chain and `SourceLadder.lean` with the actual `highLevelNext`. This includes `source_step_eq`, `source_run_eq` and source-connected return/finite blank checkpoint theorems with standard Lean axioms only. The previous CI blocker was a wrong targeted Mathlib-cache path. Changing the manually dispatched job to the established `lake exe cache get` workflow, without changing upstream mathematics, repaired it. The separate [CI 41766575228](https://github.com/FlareZ123/bb6/actions/runs/41766575228) standalone job also compiled the new `BB429Mod8.lean` against unchanged checked-in `BB429Rank.lean`.

**New all-time accelerated blank-orbit modular restriction.** [BB429Mod8.lean](BB429Mod8.lean) proves `Allowed (u,w)` is preserved by every successful exact `BB429.next` from genuine accelerated start `(0,0)`. Its modular predicate admits 17 of the 32 possible pairs `(u%8,w%4)`. The universal theorem `blank_halting_u_residue` requires every actual accelerated halting configuration to satisfy `u%8∈{1,3,5}`, excluding five u classes mod8. [BB429Extra11.lean](BB429Extra11.lean) sharpens the modular requirement to `u%16∈{1,3,5,9,13}`: for every allowed predecessor, a successor with `u%16=11` cannot have `w%4=1`, while every halt has `w+1=2u`. This is a derived necessary condition with unconditional all-natural quantified hypotheses; it does not prove Machine #429 nonhalting.

[SourceMod16.lean](SourceMod16.lean) and [SourceMod32.lean](SourceMod32.lean) transport those earlier quantified restrictions to the unchanged Cryptids accelerator via `SourceLadder.source_step_eq` and `source_run_eq`; their native-source audit succeeded in CI 41768202920. The stronger six-residue theorem and audited source bridge are detailed at the top of this dossier. The finite-modulus BFS suggestions remain computational observations except where independently certified by Lean.

These are **intermediate internal advances**, not a six-state universal census or an exact BB(6) value. Keep them under `im-results/`; external novelty remains unevaluated. The next mathematical step is to rule out a surviving genuine halt gate or produce a real blank-root halting witness rather than repeatedly increasing moduli.



**Status update (2026-11-04): substantive intermediate mathematics, native original-source bridge successfully checked in CI 41765557427. No blank-root halting decision, BB(6) exact value or universal bound.** The historical 2026-11-03 report below predates this source verification.

## Machine and mathematical semantics

The exact rooted RLE is `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`, the Cryptids #429 of the dated hard list. The original pinned [Cryptids source](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.lean) gives an exact primitive-TM acceleration to `J(u,w)`, starting at `J(0,0)` after 35 raw primitive steps, with a halting action on `w+1=2u`. The local model is `BB429.next : Nat × Nat → Option (Nat × Nat)` and `BB429.run` as defined in [Agent 5's source transcription](../agent5-429-rank/BB429Rank.lean); its exact transition branch order and truncating natural arithmetic are crucial.

Write `U(k)=3(2^k-1)`, `V(l)=14*2^l-3`. The first-branch run from root 0 has `rayDemand(k)+3k=2U(k)`, and from root 11 has `demandV(l)+3l+22=2V(l)`. Earlier conditional affine ladders are proved in [ReturnLadder.lean](ReturnLadder.lean).

## New quantified mathematical conclusions

1. **Infinite escape ray** ([EscapeRay.lean](EscapeRay.lean)): for every `u≥17`, `u%4=1`, `run 4 (u,u+8) = some (u+8,u+16)`; for every `n`, `run n (u,u+8) ≠ none`. The induction has exact all-four-state macro semantics, not a finite observed trace. A real proven entry to the ray would transfer all-time nonhalting, but no entry from the genuine blank `(0,0)` is known.
2. **Two infinite synthetic root families** ([EscapeRoot.lean](EscapeRoot.lean)): `rootU(k)+3k+1=9*2^k` for `k≥3`, `rootV(k)+3k+23=42*2^k` for `k≥1`. Starting from `(0,rootU(k))` or `(11,rootV(k))` enters the escape ray after exactly `k` accelerated steps and survives forever. These starting points are **not** the genuine blank-entry counter state.
3. **Complete U-even corridor transfer** ([ExitTransfer.lean](ExitTransfer.lean), [CorridorExceptions.lean](CorridorExceptions.lean), [WholeCorridor.lean](WholeCorridor.lean)): if `k≥6`, `k%4=2`, `w%4=0`, `w+4≤2U(k)`, then at some finite time the orbit reaches `(V(k-2),y)` with `y%4=2`, `y+4≤2V(k-2)`. The proof takes the maximal `U` ladder using `Nat.div` and `Nat.mod`, then handles *all* three possible boundary cases with exact times `2k+2`, `3k+3`, `4k+6` (each conditionally on the boundary residue). There is no unverified omitted residue.
4. **Complete V-even corridor transfer** ([VExitTransfer.lean](VExitTransfer.lean), [VWholeCorridor.lean](VWholeCorridor.lean)): if `l≥4`, `l%4=0`, `w%4=2`, `w+4≤2V(l)`, then at some finite time the orbit reaches `(V(l+1),z)` with `z%4=1`. Regular boundary `r≤3l+12` uses exactly `l+2` macro steps; the remaining `r=3l+16` uses exactly `3l+8`, visiting a root-zero U-ray. This is sector transport, not indefinite nonhalting.
5. **A fifth conditional cross-ray ladder** ([CrossRayReturn.lean](CrossRayReturn.lean)): for `l≥4`, `l%4=0`, `w%4=1`, and guard `3w+6V(l+1)+9(l+3)+36≤8U(l+3)`, the exact return is `run (2l+8) (V(l+1),w)=some (V(l+1),w+6l+60)`. A parameter-uniform induction proves arbitrarily many *guarded finite repetitions* `n`, with the final guard; it does **not** assert unlimited repetitions for fixed `l`.
6. **Real blank-origin accelerated checkpoints, proved by composing these parametric theorems:** `run 79 (0,0)=some (U(6),48)`, `run 156 (0,0)=some (U(6),356)`, `run 170 (0,0)=some (V(4),366)`, `run 186 (0,0)=some (V(5),17)` ([VWholeCorridor.rooted_to_V5_17](VWholeCorridor.lean)), and `run 202 (0,0)=some (V(5),101)` ([CrossRayReturn.rooted_to_V5_101](CrossRayReturn.lean)). These finite macro checkpoints do not improve any known world record or the global BB(6) lower bound.


## New two-stage odd-counter grammar (2026-11-03 19:37 UTC)

The following expansions are source-mirror kernel checked together with all
dependencies in [manual CI run 41704791733](https://github.com/FlareZ123/bb6/actions/runs/41704791733)
(Lean 4.36.0-rc2, standalone-proof job succeeded, `#print axioms` on principal
lemmas contains only standard Lean axioms). The separate original Cryptids
native-source build is still unverified.

1. **U odd boundary trichotomy and missing seam**:
   [OddBoundary.lean](OddBoundary.lean) proves exact two-step formulas
   for the return, `3w=2u+19` seam and strict overflow.
   Every ray `U(k)` is divisible by three, so that seam is impossible
   for all ray states; the remaining two cases are exhaustive under the
   explicit guard `w+7≤2U(k)`.
2. **Complete admissible V-odd cross-ray split**:
   [CrossRayOverflow.lean](CrossRayOverflow.lean) establishes, uniformly
   for `l≥4`, `l%4=0`, `w%4=1`,
   `3w≤2V(l+1)+1`, that the previously proven return guard gives the
   `2l+8` affine V return, while failure gives a precise `l+7`-step
   overflow `(2U-z+18,3z-2U-22)`,
   `z=2V+w+17-rayDemand(l+3)`. A ray budget
   `8V+9(l+3)+73≤12U` discharges all cap assumptions.
3. **New U-odd bounce sector**: [OddUBounce.lean](OddUBounce.lean)
   proves `run(k+4)(U(k),w)=(U(k),w+3k+31)` when `k%4=3`,
   `w%4=3` and the explicit overflow/return guards hold.
   The arbitrary finite `n` ladder is also proved.
4. **Second-stage modulo-eleven exclusion and odd V-one bounce**:
   [OddCascade.lean](OddCascade.lean) proves
   `U(2n+1)%11∈{3,10,5,7,4}`, excluding both
   possible second-stage U-ray seams
   `11w=10U(k)+107` or `11w=10U(k)+111`.
   It completes the two-level U split under stated caps,
   with strict four-step overflow
   `run 4 (U(k),w)=some ((6U(k)+68)-5w,11w-10U(k)-112)`.
   A further affine sector at `V(k)`, `k%4=1, w%4=1`,
   gives `run (k+4) (V(k),w)=some(V(k),w+3k+41)`,
   with a finite `n` ladder.
5. **More genuine blank-seed finite milestones**: compositions yield
   `run 213 (0,0)=some(513,17)`,
   `run 222 (0,0)=some(U(7),319)`,
   `run 233 (0,0)=some(U(7),371)`,
   `run 237 (0,0)=some(499,159)`,
   `run 244 (0,0)=some(V(5),313)`, and
   `run 262 (0,0)=some(V(5),425)`.
   All times count accelerated high-level map applications, not primitive
   Turing-machine steps. None proves an infinite orbit.

**Evidence classification:** These are new results within this shared
repository as far as this invocation can determine. Independent novelty
relative to wider published mathematics has not been established. Every
new statement is conditional or finite, and all new work remains in
`im-results/`. The original-source bridge is a separate open obligation.


## Further source-shaped odd-V phase (2026-11-03 19:55 UTC)

A complete 4-module extension of the conditional return grammar has now
passed full standalone Lean 4.36.0-rc2 dependency-chain CI:
[run 41707490415](https://github.com/FlareZ123/bb6/actions/runs/41707490415).
The original-source native bridge is being separately audited.

- [OddVSecondary.lean](OddVSecondary.lean) gives the exact second odd-V
  overflow \`run 4 (V_k,w)=((6V_k+48)-5w,11w-10V_k-72)\` under its
  two-step cap and overflow conditions. A further odd-odd reset and
  demand guard returns to the U_(k+2) ray after \`k+8\` macro moves.
  Rooted witness: \`run 275 (0,0)=(U_7,615)\`.
- [OddVHigh.lean](OddVHigh.lean) proves a third V-one odd affine
  sector: for \`k%4=1,w%4=1\`, \`w+7≤2V_k\`,
  \`6V_k+33≤5w\`, \`9w≤14V_k+75\`,
  the precise return is
  \`run(k+4)(V_k,w)=(V_k,w+3k+33)\`.
  Also provides an arbitrary finite bounded ladder, rooted
  \`run 286(0,0)=(V_5,553)\` and a fourfold transfer to
  \`run 322(0,0)=(V_5,745)\`.
- [OddVThirdOverflow.lean](OddVThirdOverflow.lean) derives the
  third-stage root-zero transition
  \`run 6 (V_k,w)=(0,2V_k+w+33)\` when
  \`14V_k+82≤9w\`, \`35w≤58V_k+345\`
  and the preliminary cap/overflow guards hold. With the exact U ray
  demand, \`run(k+9)(V_k,w)\` reaches U_(k+3).
  Real blank-derived witness: \`run 336(0,0)=(U_8,162)\`.
- [OddVHighReturn.lean](OddVHighReturn.lean) closes the latter
  excursion by proving the **new complete conditional high-V return**:
  \`run (2k+10) (V_k,w)=(V_k,w+6k+62)\`
  when the explicit gates above, \`k%4=w%4=1\`, and
  \`rayDemand(k+3)≤2V_k+w+33\` hold.
  Its uniform margin
  \`4V_k+30+3(k+3)≤4U_(k+3)\` guarantees the
  U-to-V reset cap for all k≥1. The theorem proves the actual
  blank-origin orbit satisfies \`run 342 (0,0)=(V_5,837)\`.

These structural results are conditional and finite. None gives a
nonhalting invariant for the original \`J(0,0)\` orbit or a universal
six-state maximum. External novelty is not established; keep under
\`im-results/\` pending outside review. The original-source bridge
requires an independent successful native-source CI build before
source-connected formal verification may be claimed.

## Reproduction and evidence quality

- **Lean:** Local Lean `4.36.0-rc2`, original Agent 5 source-equivalent arithmetic `next/run` and preserved Agent 6 helper statement definitions, checked all new modules. `#print axioms` on the principal transfer theorems and rooted witnesses produced only standard kernel foundational axioms `propext`, `Quot.sound` (and `Classical.choice` where used), no `sorryAx` or `native_decide`. The **unchanged full original modules** have *not* been compiled with the new files in a successful CI/source environment, so this evidence is accurately described as **local source-mirror kernel checked; original-source CI pending**.
- **Independent BigInt SFT:** [BB429ExitSFT.cjs](BB429ExitSFT.cjs) checks 920 boundary endpoint cases, including 23 samples of each exceptional type, across `k=6,10,...,94`; it checks all exact endpoint states/times, V-even guard, synthetic escape rays and two rooted-family samples, plus real blank-entry macro checkpoints 79,156,170. This is finite crosscheck, not universal proof.
- **Further bounded observation:** A deterministic `30,000,000`-step accelerated simulation from `(0,0)` reached `(893,110318220)` without a macro halt or any visit to the escape ray. Published upstream research reports much longer simulation. No finite observed prefix proves nonhalting.
- **External novelty:** Not independently assessed. The original Cryptids accelerated map and Agent 5/previous Agent 6 ladders are prior art; new results refine the local transition grammar. Keep these provisional intermediate contributions under `im-results/` and request independent source and novelty review before publishing.

## Open proof obligations

The true blank trajectory has not been shown to reach the escape ray; neither has an all-time blank-seed invariant excluded the halting line. The V-odd phase beyond the newly proved finite return and overflow cascades remains structurally open. Rebuild against the *unchanged original* Agent 5/Agent 6 Lean module imports, then test native Cryptids `highLevelNext` bridge in a source-matched successful CI job once GitHub Actions has recovered. Avoid repeating long uninformative traces and routine modular residue sweeps.

[Research issue](../../research/issues/R-20261103T1117Z-agent6-harmonic.md) | [Main mathematical frontier](../../results/README.md)
