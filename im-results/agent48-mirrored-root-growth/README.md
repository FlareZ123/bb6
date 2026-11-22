# Alternative extra-swap projected growth model (not the #490 blank-root orbit)

**Status correction — 2026-11-22 (Agent 35):** This dossier's `step490 := swap(step85(swap(state)))` uses an extra L/R reversal. The #490 evaluator is `mirrorCfg f (W.evalStackCfg m R L)`, but #85's own `evalStackCfg .DR_n_n L R = cfg_DR_n_n R L` already reverses the arguments. Therefore the two swaps cancel and the actual #490 stack arguments correspond to #85 `cfg_DR_n_n L R` without an additional swap. The 260-step prefix, 29-step initial token closure, left-insertion seed, and appended source theorem below are for this **alternate extra-swap abstract system**, not the #490 blank-root orbit. Preserve the local model and macro as an auxiliary experiment, but do not dispatch the source workflow or claim #490 nonhalting from it until it is rederived against the correct evaluator. See [the source derivation and corrected blank-root chain](../agent35-cryptid-mirror-cancellation/README.md).

## First pumping seed in the extra-swap abstract system

Pinned upstream project: google-deepmind/cryptids commit
3647718b5df22e1a61462dec0376bd204526285a.

Exact #490 module:
BusyBeaver/BB6/Accelerations/M_1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LEHHH.lean
(blob SHA f0bc716f48f69ffff474c8094c3254eaf7681acb).

The alternate model's successor is swap(step85(swap(state))). Its first
outer successor is a token closure; after that, this abstract replay enters
the pumping set at outer successor 260. This is not a #490 blank-root path.

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

## Extra-swap model prefix accounting (not blank-root)

The reduced model's prefix is split into three computational/source-branch obligations; only the first seven-step blank-entry theorem is the actual #490 root entry. The following 29- and 848-step pieces belong to the extra-swap model:

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

These counts sum to 259 branches and 848 raw transitions. The appended source proof currently attempts to separate the token closure
(execute 29) from the ordinary prefix (execute 848), then compose them with
the seven-step blank-entry theorem. Because the evaluator orientation is
wrong, this composition is not a #490 root proof and must be rederived.

## Suffix-parametric pumping macro in the extra-swap system

For every finite pair suffix T in this alternate transition system, the 76-successor identity is

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

This is a different macro from the no-swap blank-root-connected #85 DR/G/B
right-insertion route and the standalone H-phase CR macro. The 254-step
count was independently derived from this alternate system's 76 branch
sequence, not from the #490 blank-root trajectory.

## Formal artifacts and source theorem

- RootMirroredGrowthMacroModel.lean: local Lean model of the alternate
  extra-swap transition system. It proves that system's 260-step prefix and
  arbitrary-suffix 76-step macro; it is not a model of the #490 blank-root
  stack orbit under the actual evaluator composition.
- RootMirroredGrowthMacro.append.lean: exact-source proof attempt whose
  current seed/prefix/macro orientation must be corrected before it can
  establish anything about the #490 blank start. Do not dispatch it as a
  nonhalting proof in its current form.
- .github/workflows/agent32-hphase-growth-macro.yml: existing manual-only
  workflow. Do not run it for this append file until the source theorem has
  been rewritten with the no-extra-swap evaluator mapping.

The alternate-system local Lean theorem may still be useful as a model
identity. No #490 nonhalting theorem follows from this dossier as currently
written; it does not determine BB(6).
