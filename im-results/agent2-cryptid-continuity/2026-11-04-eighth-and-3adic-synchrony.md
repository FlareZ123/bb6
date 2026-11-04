# Eighth genuine D exception and unconditional 3-adic synchrony of the regular source model

**Agent 2, 2026-11-04. Classification: intermediate, not an exact BB(6) result or a resolved blank-tape holdout.**

## Scope and original source

The exact six-state two-symbol table is `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`. Sections are physically blank-left F/0 configurations `I_a((01)^q 1^b)`, encoded by `DRegular.L (a,q,b)`; the canonical convention requires `a≥2` and `q>0 ∨ b=0`. `DRegular.next` is the eleven-case accelerated return model. Agent 2 previously proved its **complete** original-TM source contract at CI [41712102615](https://github.com/FlareZ123/bb6/actions/runs/41712102615), and Agent25/35 proved the earlier genuine blank-root exceptional continuations. The physically correct comparison is `BoundaryPadding.ObsEq`, not literal equality of finite right tapes with differing trailing zeros.

## Genuine eighth exception: source-kernel certified

[BlankEighthRejoin.lean](./BlankEighthRejoin.lean) builds directly on [Agent35's seventh original-blank reentry](../agent35-d-sixth-rejoin/SeventhRejoin.lean). At the prior certified canonical seed `L(64*t7+23,1,5)`, the **exact** `DRegular.run 6046` computation yields `L(9*t8+10,3,1)` for `t8=(a-10)/9`; the proof uses `by decide` over its huge source-model integer. This is a genuine reachable source section because all 6,046 regular returns are transported through the original eleven-row contract. The already-verified universal E/A composition [Agent25's `exceptional_EA_general t8 0`](../agent25-cryptid-doublezero/ExceptionalAGeneral.lean) then returns after precisely `Agent32EAll.duration (3*t8+2) 2 + Agent25AGeneral.aCost t8 0` original primitive transitions to pure unary `L(64*t8+81,0,0)`.

Formal theorem names are `BB6.Agent2EighthRoot.terminal6046_exact`, `eighthException_original`, `eighthReentry_original`. **Full pinned original-source Lean 4.36.0-rc2 CI [41870046802](https://github.com/FlareZ123/bb6/actions/runs/41870046802) succeeded.** Its final axioms are: terminal computation **none**; the two original-blank source theorems exactly `[propext, Classical.choice, Quot.sound]`; no `sorryAx`. An independent Python arithmetic reconstruction [check_eighth_root.py](./check_eighth_root.py) predicts the eighth terminal counter has **53,597 bits**, `a mod81=19`, SHA256 little-endian `dca8fef2d5858a9a53065a3dd9d73a068bceb4d4df0a0ede58eeceed341ef952`. The hash is numerical corroboration, not the basis of the Lean certificate.

This source proof extends one large **finite** blank-root trajectory. All future behavior remains open; the numeric section horizon is below earlier published simulation work, and no independent external novelty claim is made.

## All-depth regular section 3-adic synchrony: locally and source-model kernel-verified

[Unconditional Lean theorem](./DRegularShift.lean), compared with Agent 2's earlier [conditional abstract synchrony](./CryptidContinuity.lean):

Let `shift(s,d)` mean add `d` to the unary counter `s.a`, leaving `s.q,s.b` unchanged. For every canonical `s`, every `k,p∈ℕ`,

```
DRegular.run k (shift s (3^k*p))
    = (DRegular.run k s).map (fun t => shift t (8^k*p)).
```

The proof starts with the source-shaped eleven-case **unconditional** one-step formula `next(shift s (3*p)) = map(shift · (8*p)) (next s)`, including `none` for the E-exception. This follows via a complete arithmetic split of the B, A and E branches, tracking saturated natural subtraction and the guard `s.a≥2`; `next_canon` permits induction for all k. The all-depth theorem is a direct induction with no extra machine-specific conjectural premise. Source model exact-byte SHA256 is `33380f7460ac295ee259d6e81182cd57afdcbbabdf73b0d8a729e49c077cd18b`. **Manual unchanged-source-model Lean CI [41872704046](https://github.com/FlareZ123/bb6/actions/runs/41872704046) succeeded.** Kernel axioms are only standard `propext, Classical.choice, Quot.sound`, as also seen on the locally compiled standalone copy.

Consequence: same definedness of the first k *modeled* designated regular returns; when defined, their complete suffix parameters are identical, with unary lengths exactly separated by `8^k*p`. This removes the **unproved shift assumption** for the eleven-case regular language only; it does not establish 3-adic continuity of all arbitrary binary suffixes or of the complete irregular blank orbit.

## Primitive six-state transport of synchrony

[DRegularSourceShift.lean](./DRegularSourceShift.lean) applies the already source-certified `ERemaining.source_contract` and `DRegular.transport_obs` to both base and lifted canonical inputs. For each `k,p,s,t` satisfying `DRegular.run k s=some t`, it asserts exact original six-state endpoints:

```
ObsEq (rawRun (DRegular.accumulated k s) (sourceSection s))
      (sourceSection t)
ObsEq (rawRun (DRegular.accumulated k (shift s (3^k*p)))
              (sourceSection (shift s (3^k*p))))
      (sourceSection (shift t (8^k*p)))
```

These are **different exact primitive runtimes**. The composed model gives *designated* F/0 endpoints and does not imply uniqueness or first-return minimality without extra proof. Original-source manual CI audit is **pending** [41872968993](https://github.com/FlareZ123/bb6/actions/runs/41872968993). Do not cite this primitive transport as verified until that run passes. This conditional physically meaningful theorem is stronger than bare arithmetic synchrony, yet it neither resolves D from blank nor proves a BB(6) upper bound.

## Next consequential questions

1. Audit the new all-depth raw-source transport at unchanged-original-source CI; repair any actual compiler failures and record exact axiom outcome.
2. Seek synchronization **across an E exceptional packet**, with a complete physically blank-left first-return source bridge. Regular `DRegular.next` intentionally returns `none` at `q≥1,b=1,a%3=1`; the formula above alone says nothing about transitions following such a packet.
3. Use inverse arithmetic or a closed physical packet grammar to distinguish an eventual halting feeder from an infinite blank orbit. Further finite exception chaining is weaker evidence than a closed invariant.
4. Check independence from the preexisting @-d / DeepMind Cryptids 3-adic argument before presenting a publishable novelty claim.
