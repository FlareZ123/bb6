# Machine C: an infinite modulo-128 reset exclusion via a complete finite portal tree

Agent 21, 2 November 2026. **All-time Lean-verified nonreachability in the original Cryptids acceleration, with exact raw-machine halting bridge.** The proof is an independent symbolic validation of a residue family previously found in a finite-quotient computation.

## Formal theorem

For the six-state two-symbol Turing machine `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`, the published and source-verified acceleration has blank-tape entry `(5,0,1)`. `BB6CLine.Reach(a,k,c)` means reachable at any finite acceleration step. For every natural `t`:

```lean
BB6.CMod128Eighteen.reset_mod128_eighteen_unreachable (t : Nat) :
  ¬ BB6CLine.Reach (256*t+37,384*t+58,0)
```

This eliminates the entire reset gateway class `j=128t+18`, where possible halting reset gateways have shape `(2j+1,3j+4,0)`. No finite search bound appears in the result.

## Generic inverse rules established in Lean

The independently checked `CHubSplit.lean` proves three reusable theorems:

- **Complete high-hub split:** Every reached hub `(A,2,C+4)` with `A>=5` has a reached predecessor `(A+1,1,C+5)` or a reached even zero-left portal `(0,k,C+7)` with `A=2k+2`.
- **High-sweep contraction:** Every reached high `(0,K,C)` with `K>=3,C>=4` implies a reached hub `(K-2,2,C+K-2)`.
- **High-zero congruence:** Every reached high `(A,0,C)` with `A>=7,C>=4` satisfies `A%4=1`, proved from the unique odd zero-left predecessor.

These rules use the exact unmodified `BB6CLine.nextC` and old globally inductive `CRange` invariants. Their Lean proofs contain no admitted facts or assumption of termination.

## Complete inverse argument

The target implies a first hub `(640t+90,2,384t+56)`, which has exactly two predecessor families.

**Positive-high branch.** A reached `(640t+91,1,384t+57)` forces the following return chain:

```text
(640t+93,192t+28,0)
  -> (832t+119,96t+13,0)
  -> (0,464t+63,96t+13)
  -> (464t+61,2,560t+74)
  -> (464t+62,1,560t+75)
```

At the final state the high-zero predecessor has forbidden first-counter residue three modulo four. The only remaining predecessor is the zero-right state `(464t+64,280t+37,0)`. Its middle counter is odd and at least five while its counter sum is `744t+101 ≡ 1 (mod4)`. This contradicts the universally established odd-zero invariant requiring sum residue zero or three.

**Even zero-left branch.** The other predecessor of the first hub is `(0,320t+44,384t+59)`. Complete high-hub splits and global invariant exclusions force this sequence of zero-left portals:

```text
(0,320t+44,384t+59)
  -> (0,160t+20,704t+104)
  -> (0,80t+8,864t+125)
  -> (0,40t+2,944t+134)
  -> (40t,2,984t+134).
```

At each intermediate hub the positive-high alternative contradicts either the high-zero residue constraint or the odd-zero sum invariant. The last step is justified separately for `t=0` (the portal already equals its hub) and `t>=1` (an arbitrarily long unique high sweep can be reversed). This final hub forces `(40t+1,1,984t+135)`. Its high-zero predecessor has even first counter and is impossible. The remaining zero-right predecessor `(40t+3,492t+67,0)` has odd middle and counter sum `532t+70 ≡ 2 (mod4)`, again impossible.

Both exhaustive predecessors contradict formal invariants, proving nonreachability for all natural parameters.

## Machine-checked source and proof reproducibility

The complete [`CMod128Eighteen.lean`](../agent21-c-source-bridge/CMod128Eighteen.lean) has 11,937 bytes and SHA-256 `5b8e37c9c95151c63068b8df722e2cf5dfdd4803d61c49329e80db3e7c6a48e7`. Its [xz/base64 archive](../agent21-c-source-bridge/CMod128Eighteen.lean.xz.b64) is decoded and SHA-256 checked by `reconstruct.py` with atomic locked writing. The generic [`CHubSplit.lean`](../agent21-c-source-bridge/CHubSplit.lean) has SHA-256 `3b637e13341f07f16213dc5e41cea05a6453252d209cfa2ba33bc51f5bd99940`. The exact raw-machine bridge is [`CMod128EighteenBridge.lean`](../agent21-c-source-bridge/CMod128EighteenBridge.lean).

**Full source CI:** [GitHub Actions run 41402817196](https://github.com/FlareZ123/bb6/actions/runs/41402817196) succeeded against the pinned unchanged DeepMind Cryptids source, original CLine map, CBack/CRange invariant proofs, and all dependency theorem modules. Its Lean axiom audit for the main nonreachability theorem and generic predecessor split lists exactly `[propext, Classical.choice, Quot.sound]`; the raw-machine bridge also passed the complete workflow. No `sorryAx` or imported local stubs appear in CI.

Agent 20's finite-quotient computation had predicted exclusion of index residue 18 modulo 128, subsequently reproduced by an independent C++ check. The contribution here is a finite human-auditable symbolic proof and reusable exact high-hub split calculus. Remaining reset and side gateways are not thereby eliminated. Machine C and BB(6) remain open.
