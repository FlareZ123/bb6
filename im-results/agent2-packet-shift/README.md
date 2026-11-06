# Arbitrary-tail D packet-path 3-adic synchronization (Agent 2, 2026-11-05)

**Classification: intermediate original-source theorem. No blank-tape nonhalting decision, BB(6) bound, external novelty claim, or global return-language closure.**

Original six-state binary machine: `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`. The physically explicit packet configurations are those defined by [Agent31 PacketSource](../agent31-d-exceptional/PacketSource.lean):
`M(a,q,p;Y)=I_a((01)^q 0 1^p Y)`, for an **arbitrary finite binary tail Y**. The original-source B and E guarded packet edges were already proved in [Agent31 PacketPaths](../agent31-d-exceptional/PacketPaths.lean), source run [41698072765](https://github.com/FlareZ123/bb6/actions/runs/41698072765). They preserve the entire Y.

## New theorem, exact scope

[PacketShift.lean](./PacketShift.lean) imports the **unchanged** Agent31 `PacketPaths`, and proves the following for **every** `Path s n T dst` made of n guarded B/E packet edges and every natural `x`:

* There is a valid n-edge path from `shift s (3^n*x)` to `shift dst (8^n*x)`, with unchanged packet q,p and arbitrary untouched tail Y.
* Its exact source-machine primitive runtime satisfies
  `T(x)=T+L*x+Q_n*x*x`, for a natural integer L determined by the path.
* The universal quadratic coefficient `Q_n` depends **only on n**, not on path choices, source counters or tail:
  `Q_0=0`, `Q_(n+1)=12*9^n+64*Q_n`, and
  **`55*Q_n + 12*9^n = 12*64^n`**.
* The theorem `BB6.Agent31PacketShift.source_path_shift` uses `PacketPaths.path_sound` and asserts **literal equality of raw original Turing-machine configurations** at those exact timestamps, for each x and Y.

**Authenticated original source:** manually dispatched workflow [42082379928](https://github.com/FlareZ123/bb6/actions/runs/42082379928) (2026-11-05 18:14Z), head `07b1401eb6b6118372d7edffb78aefee28843766`, passed its actual compiler step in ~23 seconds. The workflow restores the checksum-pinned original `CryptidBoundary` six-state machine and source B/E macros; it compiles unchanged `PacketSource`, `PacketPaths`, then `PacketShift` using Lean 4.36.0-rc2. The log reports `[propext, Quot.sound]` for **all four new theorems**, including `source_path_shift`; no `sorryAx` and no extra declared axioms. Reproduction workflow: [agent2-packet-shift.yml](../../.github/workflows/agent2-packet-shift.yml), manual only.

## Representative full physical tape check

One legitimate two-edge path is `M(2,1,3;Y) -> M(10,0,3;Y) -> M(25,2,0;Y)`, with baseline time `40+204=244`. The theorem specializes to

```
M(2+9x,1,3;Y) -> M(25+64x,2,0;Y)
T(x) = 244 + 923x + 876x²
```

where both sides have precisely the same arbitrary Y. An independent literal eleven-action raw simulator compared the two physical F/0 endpoints, initial/final entire nonblank tape and their primitive elapsed times at `x=0..11` for Y=`''`, `'1'`, `'010111'` and `'111100101'`. All **48 independent cases** passed. It canonicalized trailing explicit zero as implicit physical blank. These finite checks are ancillary to the source-kernel proof.

## Relationship to prior internal work

The universal `Q_n` polynomial already appeared in [Agent2 regular D path theorem](../agent2-cryptid-continuity/DRegularTimedShift.lean) and authenticated source counterpart [DRegularSourceShift](../agent2-cryptid-continuity/DRegularSourceShift.lean), original-source CI [41872968993](https://github.com/FlareZ123/bb6/actions/runs/41872968993). The genuinely broader **domain here** is arbitrary binary tails during guarded packet paths, outside the fixed 11-case regular L language. The shared quadratic curvature is therefore a compatibility identity, **not** an independently new coefficient. The packet rank decreasing by one per guarded edge was already source-certified by Agent31. This result does not cover arbitrary E-low-p exits, A returns, the halt state, or first-return minimality where earlier F/0 passes are physically possible.

## Unresolved decisive question

The real blank orbit can leave regular `L` at an E exception. A B/E packet phase of at most q+p edges is source-certified, but its **exits** (A, B q=0, E p=0,1,2) are not controlled by this theorem. A globally closed source-connected physical word language or full halt-gate obstruction is still missing. It is not valid to deduce nonhalting from path synchrony, from a long finite blank-root certificate, or from a synthetic source path. Future work should compose the packet exit rules into an invariant for the genuine rooted orbit and audit external originality.


## 2026-11-05 exceptional E suffix rotation, two independently certified boundaries

The first low-p exception has now been source-composed with **arbitrary preceding guarded B/E paths** in [PacketEscape.lean](./PacketEscape.lean), [successful full original-source CI 42083875759](https://github.com/FlareZ123/bb6/actions/runs/42083875759), with [propext, Quot.sound] only and no admitted axioms.

For all k,q,Y the extra E boundary is the **exact** source equality

```
M(3k+4,q,2; 0111Y)
  --[12k²+49k+68+4q]-->
M(8k+5,0,2q+6; 01010Y).
```

Appending this gate to **any** n-edge guarded packet path (ending at `M(3k+4,q,2;0111Y)`) preserves the complete source execution after input unary lift `3^(n+1)*x` and output unary lift `8^(n+1)*x`. The total elapsed primitive time again has universal quadratic `Q_(n+1)`, even though this exceptional gate increases packet rank and changes the tail.

**New second tail theorem** [ELowSecond.lean](./ELowSecond.lean), independently source-checked by [CI 42084654996](https://github.com/FlareZ123/bb6/actions/runs/42084654996), states an additional universal source rule for **all k,q,Y**:

```
I_(3k+4)(0 (10)^q 1101010111 Y)
  --[12k²+49k+80+4q]-->
I_(8k+5)(0 1^(2q+6) 010101010 Y).
```

The proof is a 32-step A-on-0 `1101010111` turnaround that holds for *any* unknown left tape, followed by previously source-certified arbitrary-q C reverse scan, two-step B handoff, and D closing sweep. It is an exact quantified raw source equality, not numerical interpolation. It specializes to the second relevant tail reset

```
M(3k+4,q,2; 01010111Y)
  --[12k²+49k+80+4q]-->
M(8k+5,0,2q+6; 010101010Y).
```

These are **synthetic E-section rules** and do not establish that the genuine blank root reaches any chosen packet input. A numerical observation about a potential *third* tail reset remains unproved: for q≥1 the apparent right tape becomes `0 1^(2q+2) 0 1^14` at F/0; q=0 follows a different branch. Do not promote this observation to a theorem without a source-connected proof. No result here settles BB(6) or even this D holdout.

## 2026-11-05 20:20 UTC: source-certified generic turn, overlap correction

Original-source CI [42101721465](https://github.com/FlareZ123/bb6/actions/runs/42101721465) succeeded after repairing the zero-index normalization `run 0` in `ATurnFamily.lean`. `EGenericTurn.full_E_from_turn` is a reusable original-table compiler: a finite A/0-to-C/1 local turn of length N preserving every unknown left tape and right suffix supplies a complete F/0 E return of exact duration `12k²+49k+N+48+4q` for arbitrary k,q and suffix. The proof does not assert a first-physical return or true-blank reachability.

`ATurnFamily.a_turn_all` establishes such turns for `11(01)^(r+1)11`. The derived `EAltPacket.e_alternating_source` passed unchanged-original-source CI [42102221441](https://github.com/FlareZ123/bb6/actions/runs/42102221441) without `sorryAx`, showing for all k,q,r and all binary tails Y:

```text
M(3k+4,q,2; (01)^(r+1)11Y)
  --[12k²+49k+6r+68+4q]-->
M(8k+5,0,2q+6; (01)^(r+2)0Y).
```

**Novelty correction:** This equation is *literally equivalent* to Agent37's earlier `im-results/agent37-root-language-pilot/EAlternatingTriple.lean` theorem `full_E_alternating_triple`: its input `I_(3k+4)(0(10)^q 110(10)^r111Y)` and output `I_(8k+5)(0 1^(2q+6)(01)^(r+2)0Y)` represent the same physical configurations with the identical time. Therefore `EAltPacket` is an independent source-checked derivation and packet-calculus integration, with **no distinct new halting exclusion, root decision, or BB(6) bound**. Keep in `im-results/`. For this exact family, reuse Agent37's prior work instead of counting a new frontier theorem.

An unbounded arbitrary-local-turn E compiler may assist other suffix-sensitive packet exits, but source first-event minimality and genuine blank-orbit applicability remain open.

## 2026-11-05: verified marked-F return compiler and two-index 110(10)^r0 gate

The original-source `EAltBoundaryFirst.boundary_first_from_local_noF_turn` and `EGenericFullFirst.full_E_from_noF_turn_first` have succeeded in manual Lean CI [42104742759](https://github.com/FlareZ123/bb6/actions/runs/42104742759). They turn any left/suffix-preserving, F-free A0->C1 local turn into a complete exact-first-physical E branch.

Stronger lemmas `boundary_first_from_local_noPhysical_turn` and `full_E_from_noPhysical_turn_first` passed the unchanged-source Lean CI [42106984785](https://github.com/FlareZ123/bb6/actions/runs/42106984785). They allow interior F/0 visits with a marked, physically nonblank left side. Standard Lean axioms only; no `sorryAx`.

The new two-index local turn `AIterDoubleZero.a_double_zero_turn` passed [CI 42106130346](https://github.com/FlareZ123/bb6/actions/runs/42106130346): for every v,r,L,Y, A0 on `(10)^(v+2)110(10)^r0Y` reaches C1 on `1^(2v+1)0 1^(2r+6)Y` in `4v+4r+20` original transitions. `AIterDoubleZeroFirst.a_double_zero_turn_noPhysical` passed [CI 42106756345](https://github.com/FlareZ123/bb6/actions/runs/42106756345).

Composing this with the stronger first-event compiler, [CI 42106984785](https://github.com/FlareZ123/bb6/actions/runs/42106984785) certified `EIterDoubleZeroFullFirst.full_E_double_zero_first_physical` for every k,q,v,r,Y: canonical input `I_(3k+4)(0(10)^(q+v+2)110(10)^r0Y)` first physically blank-left F0 returns in `12k²+49k+4(q+v+2)+4r+60` transitions to `I_(8k+5)(0 1^(2(q+v+2)+2)0 1^(2r+6)Y)`. `EIterDoubleZeroPacket.lean` is a separate ongoing Lean normalization of the canonical words, not a requirement for the already certified raw-list theorem.

Prior work: r=0 overlaps the already formalized E-1100 branch. Agent37 had independently conjectured this general `110(10)^r0` A-turn in an earlier incarnation and documented a locally checked mock (see agents/agent37/memory.md); this contribution is original-source certification with strict physical minimality, not priority to the conjecture. Agent37 was informed through communications/agent37/20261105T2053Z_agent2-110-ten-r-zero-certified.md.

No result claims authentic blank-root reachability, a BB6 bound, or a halt decision. Preserve these synthetic first-return tools in `im-results/`.


## 2026-11-06: all-initial-pair-count exceptional E boundary endpoints

**New source-authenticated original-machine endpoint theorems**, independently compiled under the unchanged six-state transition table using Lean 4.36.0-rc2:

- [EZeroPump.lean](./EZeroPump.lean), [successful original-source CI 42144177148](https://github.com/FlareZ123/bb6/actions/runs/42144177148): for all k,r≥0 and every finite binary Y,
  **I_(3k+4)(0 110 (10)^r 0 Y) → I_(8k+3)(0 1111 0 101010 1^(2r) Y)**
  in exactly **12k²+49k+96+4r** original primitive transitions. The theorem full_exceptional_pump generalizes Agent32's full_E_zero_pairs (r=0), using an A forward / C reverse scan and a source-checked 13-step synchronization with Agent32's unchanged boundary.
- [EOneZero.lean](./EOneZero.lean), [successful original-source CI 42145329321](https://github.com/FlareZ123/bb6/actions/runs/42145329321): for all k,r,Y,
  **I_(3k+4)(0 10 110 (10)^r 0 Y) → I_(8k+5)(0 1^4 0 1^(2r+6) Y)**
  in exactly **12k²+49k+64+4r** primitive transitions. Its new a_one_zero_turn is an all-context A/0-to-E/1 rule for 10110(10)^r0 Y taking 16+4r steps and preserving every left tape and Y. A fixed E/1-to-D/0 eight-step rule completes the source return.
- [EIterDoubleZeroFullFirst.lean](./EIterDoubleZeroFullFirst.lean) and [EIterDoubleZeroPacket.lean](./EIterDoubleZeroPacket.lean), previously source-certified [CI 42107775516](https://github.com/FlareZ123/bb6/actions/runs/42107775516), handle every q≥2, r≥0, Y:
  **I_(3k+4)(0 (10)^q 110 (10)^r 0 Y) → I_(8k+5)(0 1^(2q+2) 0 1^(2r+6) Y)**
  at **12k²+49k+60+4q+4r** raw steps, with formal exact first physically blank-left F/0 return.

Together these three source-connected formulas supply **every q≥0** for the exceptional suffix family 0(10)^q110(10)^r0Y, with separate q=0 and q≥1 regimes. They share the input unary lift k→k+1 with output unary +8 and return-time difference **24k+61**, for fixed q,r,Y. Each new theorem's axiom audit is exactly [propext, Quot.sound], with no sorry or additional evaluation axioms.

[check_e_zero_family.py](./check_e_zero_family.py) is a separate literal twelve-transition sparse-tape first-event simulator. It tested **4,992** deterministic instances across k=0..7, q=0..5, r=0..12, and eight binary suffixes. Every instance reached its predicted source endpoint and time at the first *physically blank-left F/0* event, without an earlier halt. This finite observation motivates proving first-event minimality for q=0 and q=1. Those two minimality claims are **not yet Lean-certified**; q≥2 minimality is certified.

This completes an all-initial-pair-count special-word gate **for synthetic F/0 sections**. The actual blank-tape trajectory has not been shown to visit any arbitrary member of this family. There is no nonhalting conclusion, new champion bound, exact BB(6), or externally established novelty. Keep these lemmas and regression in intermediate storage pending a rooted application. A useful next task is incorporation into Agent31's arbitrary-tail packet transducer and Agent37's proposed irregular first-event 3-adic coupling, particularly E,p=2 exits from decreasing-rank packet phases.
