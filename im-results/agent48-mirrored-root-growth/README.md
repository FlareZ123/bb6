# Corrected #490 mirrored-root nonhalting proof attempt

**Status: decisive exact-source proof attempt pending CI.** The corrected mirrored-root replay identifies the pumping invariant after only 260 outer successors, not 1,153,484. A local Lean model proves the 260-step outer-stack prefix after representing the initial token-closure endpoint explicitly, and proves the 76-step suffix-parametric macro. The appended exact-source theorems attempt to prove the token closure, ordinary prefix, pumping macro, and resulting nonhalting invariant directly against the pinned original #490 machine. Do not claim nonhalting until the manual source workflow succeeds and the axiom profile is clean.

## First root-reachable pumping seed

Pinned upstream project: google-deepmind/cryptids commit
3647718b5df22e1a61462dec0376bd204526285a.

Exact #490 module:
BusyBeaver/BB6/Accelerations/M_1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LEHHH.lean
(blob SHA f0bc716f48f69ffff474c8094c3254eaf7681acb).

The corrected #490 mirrored successor is swap(step85(swap(state))). The
first outer successor is a token closure; after that, the ordinary root
replay enters the pumping set at outer successor 260.

At that first seed, the state is DR with left length 31 and right length 14.
Write

    B = [0,2,0,0,0,2,0,0,0,16,0,0]
    R0 = [0,1,0,0,0,0,0,0,0,0,1,0,0,0]
    T0 = [0,12,0,0,0,12,0,0,0,12,0,0,0,2,0,0,0,0].

Then the seed is exactly

    DR(L=[1] ++ B ++ T0, R=R0).

The tail T0 has length 18. The same fixed prefix and right stack are visible
at the later 750,000 and 1,153,484 checkpoints. Those are 9,865 and 15,174
iterations, respectively, of the 76-successor macro after seed 260:

    750000 - 260 = 9865 * 76
    1153484 - 260 = 15174 * 76.

The long replay is therefore no longer the root-entry bottleneck.

## Root-prefix raw-step accounting

The blank-root entry is split into three exact source obligations:

| Segment | Raw TM transitions | Outer-stack successors |
|---|---:|---:|
| Blank root to initial DR stack state | 7 | — |
| Initial token closure DR to CR | 29 | 1 |
| Ordinary CR-to-seed prefix | 848 | 259 |
| **Total to first pumping seed** | **884** | **260** |

The 29-step token closure consists of the source branch's 3-step entry
followed by token reductions of 2 + 21 + 2 + 1 steps. The 259 ordinary
branches have cost 848. Their source-mode branch counts are:

- CR head 0: 42 at 2 steps
- CR prefix 1,empty: 2 at 6 steps
- EL head 0: 59 at 2 steps
- EL positive: 40 at 1 step
- DL positive (at least 2): 14 at 4 steps
- DR left head 0 / positive right: 31 at 4 steps
- DR empty-left-tail: 4 at 1 step
- DL head 0: 26 at 6 steps
- DR positive/positive: 9 at 3 steps
- CR empty: 2 at 2 steps
- EL empty: 1 at 1 step
- CR prefix 1,0: 22 at 5 steps
- CR prefix 1,1: 7 at 16 steps

These counts sum to 259 branches and 848 raw transitions. The appended
source proof separates the token closure (execute 29) from the ordinary
prefix (execute 848), then composes with the 7-step blank-root entry.

## Suffix-parametric pumping macro

For every finite pair suffix T, the 76-successor identity is

    DR(L=[1] ++ B ++ T, R=R0)
      --76 outer successors-->
    DR(L=[1] ++ B ++ B ++ T, R=R0).

The right stack is unchanged; the left stack gains exactly 12 entries; the
entire suffix is preserved; and no token-normalizer branch occurs. Seven
explicit suffix regressions passed. The local Lean model proves the
outer-rule identity for arbitrary pair suffixes.

The 76 underlying source-branch counts are independently audited:

| Source branch | Count | Cost each | Subtotal |
|---|---:|---:|---:|
| DR, left head 0 / positive right head | 8 | 4 | 32 |
| DR, positive left and right heads | 3 | 3 | 9 |
| CR, left head 0 | 13 | 2 | 26 |
| CR, left prefix 1,0 | 8 | 5 | 40 |
| CR, left prefix 1,empty | 1 | 6 | 6 |
| EL, right head 0 | 16 | 2 | 32 |
| EL, positive right head | 12 | 1 | 12 |
| DL, right head at least 2 | 4 | 4 | 16 |
| DR, empty left tail | 1 | 1 | 1 |
| DL, right head 0 | 8 | 6 | 48 |
| CR, left prefix 1,1 | 2 | 16 | 32 |
| **Total** | **76** |  | **254** |

This is a different macro from the old #85 synthetic DR/G/B route and the
standalone H-phase CR macro. The 254-step count was independently derived
from the mirrored root's actual 76 branch sequence.

## Formal artifacts and source theorem

- RootMirroredGrowthMacroModel.lean: local Lean 4.36.0-rc2 model. It proves
  the 260-step outer-stack root prefix after representing the initial token
  closure endpoint explicitly; it proves the arbitrary-suffix 76-step macro;
  and it checks the 848, 877, and 254 arithmetic. The token endpoint in this
  reduced model is not itself a source proof.
- RootMirroredGrowthMacro.append.lean: exact-source proof attempt in the
  pinned #490 module. It proves (or will fail to prove) the 29-step token
  closure, 848-step ordinary prefix, 7-step blank-root entry, 254-step
  pumping macro, and finally applies IsNotHalt.of_reachesPlus_invariant to
  the fixed-prefix/right-stack set.
- .github/workflows/agent32-hphase-growth-macro.yml: existing manual-only
  workflow repurposed for this exact source proof. The older H-phase append
  file is preserved but is not part of this run.

If all source theorems compile with no sorryAx in their transitive axiom
profiles, root_mirrored_isNotHalt proves that the #490 blank-start machine
does not halt. That would classify this particular machine as nonhalting,
not determine BB(6). The exact CI result is still pending.
