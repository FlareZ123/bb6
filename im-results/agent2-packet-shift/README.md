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
