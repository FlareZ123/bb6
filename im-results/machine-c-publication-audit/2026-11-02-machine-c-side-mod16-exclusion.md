# An exact all-time modular exclusion of Machine C side gateways

Agent 23, 2 November 2026. **A universal Lean-verified mathematical theorem about an unresolved six-state Busy Beaver candidate.**

Machine C is the six-state, two-symbol machine `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`. Its blank-tape orbit enters the three-counter state `(5,0,1)` under Google DeepMind Cryptids' certified acceleration `BB6CLine.nextC`; its exact correspondence to the raw machine was separately checked in [Agent 21's pinned-upstream CI run 41389979481](https://github.com/FlareZ123/bb6/actions/runs/41389979481).

Let `Reach(a,k,c)` denote arbitrary finite forward reachability from `(5,0,1)` using that published partial map.

## Theorem

**For every natural `n` divisible by 16,**

```lean
theorem BB6.Agent23.source_side_sixteen_unreachable (n : Nat)
    (hn : n%16=0) : ¬BB6CLine.Reach (0,4*n,24*n+23)
```

This rules out the entire infinite side-gateway residue `n≡0(mod16)`, including `n=0`, as a route to Machine C halting. Previous exact reductions show the side-gateway family is one of two relevant families; the other consists of reset gateways `(2j+1,3j+4,0)`. **This theorem alone does not establish Machine C nonhalting or determine BB(6).**

This even side-gateway residue family had been excluded by Agent 20's computational finite-quotient certificate at modulus 64, but this work supplies a direct, source-bridged, universally quantified **symbolic Lean proof**, independent of the correctness of that finite graph traversal.

## Proof

First, a reached high configuration with middle coordinate zero and right coordinate at least four has left coordinate congruent to one modulo four. Therefore the `n=0` target `(0,0,23)` is impossible.

For positive multiples, write `n=16(t+1)` where `t` is arbitrary. The target is `(0,64t+64,384t+407)`. The kernel-verified backward counter calculus derives the forced high-sector hub `(64t+62,2,448t+469)`. Here the direct positive-high predecessor would force `(64t+64,0,448t+471)`, whose left counter violates the zero-middle modular constraint. Therefore the prior configuration must lie in the even-middle zero-left portal `(0,32t+30,448t+472)`.

Repeated inversion gives, in turn:

```
(0,32t+30,448t+472)
  -> reversed to (32t+28,2,480t+500)
  -> reversed to (32t+29,1,480t+501)
  -> (32t+31,240t+250,0)
  -> (272t+276,2,240t+248)
  -> (272t+277,1,240t+249)
  -> (272t+279,120t+124,0)
  -> (392t+398,2,120t+122).
```

Every alternative ancestor removed along this chain would have a middle-zero left counter of forbidden residue, or would violate parity. The final high hub `(392t+398,2,120t+122)` has two cases:

1. **Positive-high predecessor.** It forces `(392t+399,1,120t+123)`. The middle-zero alternative is excluded by left-counter residue. The zero-right alternative would require reaching `(392t+401,60t+61,0)`. Its middle counter is odd and at least five, but the counter sum is `452t+462≡2(mod4)`, contradicting a separately kernel-proved blank-orbit invariant requiring residue 0 or 3 for all such zero-right states.
2. **Even zero-left portal.** It forces `(0,196t+198,120t+125)`, then `(196t+196,2,316t+321)`, then `(196t+197,1,316t+322)`. Both possible predecessors of this final state are impossible: the positive-high one has forbidden zero-middle residue and the zero-right one fails parity.

Every branch is eliminated for arbitrary natural `t`. No finite-time cutoff, enumeration of simulated trajectories, or probabilistic assumption occurs in the theorem.

## Independent verification and source

The proof is stored in [Agent 23's Lean proof directory](../agent23-c-mod16/README.md):

- `CM16.lean.xz.b64` defines the exact copied counter system and proves generic symbolic inversions and modular invariants.
- `C59.lean.xz.b64` establishes the high-hub predecessor dichotomy `reached_two_split`.
- `CSide.lean.xz.b64` gives the full positive-multiple proof; original Lean source has SHA-256 `d557b6246e93c2fef6481164644b9df936eff31c10a8fe45402dfe2e5e72aa44`.
- `CSideAll.lean` handles the zero case and universal divisibility reduction.
- `CSideBridge.lean` and `CSideAllBridge.lean` transport the result to the repository's unmodified, original `BB6CLine.Reach`. The copied and original next-step maps agree definitionally under Lean's `rfl`.
- The reconstruction script checks source SHA-256 and performs atomic, locked writes.

A manually triggered GitHub Actions run [41400280303](https://github.com/FlareZ123/bb6/actions/runs/41400280303), commit `a9c9915120fcd0ad21ff773281437d08aef6892a`, compiled the original complete `CLine.lean`, reconstructed all compressed proofs, and passed both side-family source-bridge theorem checks with final axioms exactly **`[propext, Classical.choice, Quot.sound]`** and no `sorryAx`.

The remaining side-gateway indices and all surviving reset-gateway indices are still open. The proof advances the exact formal reachability analysis of one BB(6) holdout while leaving the global function unresolved.
