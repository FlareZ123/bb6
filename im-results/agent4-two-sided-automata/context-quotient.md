# Context-congruent quotient of finite two-stack nonhalting relations

**Status (2026-11-28):** new, reproducible *computational reduction*, not yet a
kernel-accepted compressed nonhalting theorem. The uncompressed M42763 Lean
certificate already passed [run 46127222127](https://github.com/FlareZ123/bb6/actions/runs/46127222127).
The corresponding original-source M23706 and M39232 sharded proofs and the
minimized-source checks were launched separately; acceptance must be determined
from their actual final Lean axiom profiles, not from the statistics below.

## Mathematical construction

For a two-stack certificate let `R ⊆ Q × {0,1} × L × U` be the finite
control/read/left/right relation, `P_L,P_U` the sets of inverse-pop edges,
and `δ_L,δ_U` the (possibly partially recorded) deterministic push maps.
The original `TwoSidedAutomata.check` proves that the blank initial
configuration is in `R`, no configuration reaches an undefined rule, and
every enabled move/push/inverse-pop successor remains in `R`.

Give every left stack state the **complete context signature**

```
C_L(l) = { (q,b,u) : (q,b,l,u) ∈ R }
```

and every right state the dual signature

```
C_U(u) = { (q,b,l) : (q,b,l,u) ∈ R }.
```

Group equal signatures, then repeatedly refine a group whenever members have
different current equivalence classes of either *recorded* push successor,
including a distinct sentinel for an unrecorded successor. The resulting
equivalences are push-congruent wherever the original relation exercises the
pushes. Project `R`, both inverse-pop edge sets and both push maps to the
new classes; include each original edge once and each original configuration
once. The blank bottom class is assigned index 0.

**Why closure is preserved.** Fix a projected configuration and a projected
pop edge. Choose an original witness configuration `(q,b,l,u)∈R`. The
projected pop edge arises from some original state `z'` in the same class as
the popped-side state `z`. Equal *complete* opposite-side context signatures
guarantee that replacing `z` by `z'`, while keeping the same control and
other-side original state, yields another tuple in `R`. The original
closure condition supplies the corresponding successor. Push congruence
makes its pushed stack representative land in exactly the projected target
class. Hence that successor lies in the projected relation. The initial
blank membership and absence of a halt transition survive projection.
This gives the finite-relation quotient principle; it does **not** by itself
turn untrusted source code into a trusted nonhalting proof.

The [implementation](minimize_relation.py) recomputes every projected
successor from scratch, independently checks inverse-edge consistency and
blank-bottom inclusion, and raises on any missing relation successor. The
**actual proof gate** remains the *unchanged* Lean
`TwoSidedAutomata.check` and its `Agent4Automata.never` theorem. The
quotient's arithmetic, context signatures, and generator are outside the
trusted kernel.

## Exact candidate sizes

The independent in-invocation deterministic relation enumerator reproduced
all three original exact fixed points, then verified **zero missing projected
successors** after congruence refinement:

| Original one-hole TM | Original (joint, left, right) | Context quotient (joint, left, right) | Joint decrease |
| --- | ---: | ---: | ---: |
| M23706 | (9,299, 194, 734) | (4,653, 165, 353) | 49.96% |
| M39232 | (19,013, 141, 933) | (3,565, 113, 209) | 81.25% |
| M42763 | (3,142, 103, 677) | (791, 82, 157) | 74.83% |
| **Together** | **(31,454, 438, 2,344)** | **(9,009, 360, 719)** | **71.36%** |

This is a reduction of the *certificate relation*, not of the actual TM run
length, the space of machines, or the global BB(6) undecided count.
It can reduce enormous proof-term tries and the number of Lean evaluation
steps required to recheck their soundness.

## Reproduction and acceptance

- Original exact fixed points:
  `im-results/agent4-raw56-root-pilot/m{23706,39232,42763}_block_cert.py`.
- Source-preserving optimized wrappers:
  `m23706_min_cert.py`, `m39232_min_cert.py` in that directory.
  They verify the original expected triple *before* quotienting, and the
  smaller expected triple *after* independently checking projected closure.
- Shared quotient implementation: `minimize_relation.py` alongside this
  note. The [sharded source emitter](../agent4-raw56-root-pilot/m_block_split.py)
  accepts `--minimized` for 23706 or 39232; the [single-source emitter](../agent4-raw56-root-pilot/m_min_single.py)
  can attempt an ordinary Lean `by decide` check of the substantially smaller
  certificate.
- Manual workflows:
  `.github/workflows/agent4-two-stack-minimization.yml` (Python
  reproducibility), `.github/workflows/agent4-min-two-stack.yml` (full
  Lean original-source acceptance), and
  `.github/workflows/agent4-raw56-lb.yml` (fallback 16-way row sharding).

**No theorem-status upgrade follows from the raw program's assertions,
source generation, this note, or a queued CI run.** Only successful
original-source kernel compilation and the strict standard-axiom gate
establish an accepted nonhalting theorem. A full Raw56 1LB Cover additionally
requires all six originals and the six-residual parent join.
