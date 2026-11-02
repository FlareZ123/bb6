# Agent 22: unbounded generic inverse paths for Sheep halting powers

**Scope and evidence:** These are intermediate but universally quantified results about the exact one-variable return graph of the six-state Sheep Machine. All three modules compiled under Lean 4.36.0-rc2 and in the pinned Cryptids GitHub Actions workflow [run 41392634957](https://github.com/FlareZ123/bb6/actions/runs/41392634957) (successful 2026-11-02 05:17 UTC). Final theorems report only `[propext, Quot.sound]` and no `sorryAx`. The two-counter-to-original-Turing-machine semantic bridge for **this very graph** is separately machine-level certified in `im-results/agent22-sheep-semantic-bridge/`. This result does not decide any six-state machine, determine BB(6), improve a BB(6) bound, or assert external novelty.

## Main theorem: arbitrarily deep *genuine* inverse paths

The Sheep return graph on positive integers `t=2^a u` (odd `u`) has a generic nonhalting transition `t -> t+a+(u-1)/2` whenever `u>=5`. In particular, for any odd `u>=5`,

```text
u -> (3u-1)/2
```

is a real `a=0` generic edge. Equivalently, if a target `y` has `2y+1` divisible by 3, it has generic predecessor `(2y+1)/3`, provided that predecessor is odd and at least five.

For **every natural depth `n`** and **every positive modulus `m`**, there are **infinitely many distinct exponents `j` divisible by `m`** whose halting powers have a concrete, valid chain of **exactly `n`** generic Sheep return edges. The first formal theorem supplies an explicit witness:

```lean
theorem BB6.Agent22.GeneralAncestry.every_modulus_has_unbounded_inverse_chains
    (m : Nat) (hm : 0 < m) (n : Nat) :
    ∃ j t : Nat, m ∣ j ∧ SectionChain n t (2^j)
```

`SectionChain` is defined recursively using the **actual** `SheepBridge.SectionNext` relation; every displayed edge is verified to be generic with `a=0`, `u` odd and `u>=5`. The stronger `arbitrarily_large_exponents_have_deep_chains` theorem proves `∀ m>0,n,K, ∃ j>K,t, m∣j ∧ SectionChain n t (2^j)`, thereby supplying infinitely many such powers in every zero-modulus residue class. Both are fully quantified Lean theorems of actual return edges.

### Explicit construction

`InfiniteAncestry.lean` proves by cubic exponent-lifting that for every `k` there is a positive integer `Q(k)` such that

```text
2^(2*3^k) = 1 + 3^(k+1)*Q(k),       Q(k+1)>=4.
```

`PeriodicAncestry.lean` establishes an exact quotient operator `W`:

```text
(1 + d*q)^h = 1 + d*W(d,q,h).
```

`GeneralAncestry.lean` chooses, for arbitrary `m>=1` and `n>=0`,

```text
j = (2*3^(n+1))*m,
q = W(3^(n+2), Q(n+1), m),
A_i = 1 + 2^i * 3^(n+2-i)*q,     0 <= i <= n.
```

Here `2^j=A_0` and `q>=4`. Every `A_(i+1)` is odd, at least 9, and satisfies `3*A_(i+1)=2*A_i+1`. Thus `A_(i+1) -> A_i` is a valid generic Sheep transition. The sequence `A_n -> A_(n-1) -> ... -> A_0=2^j` is an explicit `n`-edge chain. All identities and admissibility checks are formal Lean proofs, valid at arbitrary `n,m`.

`PeriodicAncestry.lean` also states the original specialization for `m=5400`, the period used in Agent 17's inverse-tree sieve:

```lean
theorem BB6.Agent22.PeriodicAncestry.class_zero_has_arbitrarily_deep_generic_ancestry
    (n : Nat) : ∃ j t, 5400 ∣ j ∧ SectionChain n t (2^j)
```

## Consequence for inverse-sieve research

Consider a proof method that tries to eliminate **every** halting power in an exponent residue class by building a fixed-depth inverse tree and proving that each leaf lacks any predecessor. For the zero residue class modulo any chosen positive modulus, **no such uniform fixed depth can succeed**: the above theorem supplies a target in that same class with a genuine all-generic inverse chain extending beyond the depth. Any complete solution must incorporate additional information, especially the blank-start reachable set, or allow a fundamentally different unbounded-depth invariant.

These constructed predecessor states are **not known to be reachable from the actual initial section state `t=5`**. The theorem therefore leaves Sheep halting undecided. It does not rule out other certificate styles, such as fixed-depth trees that close branches through stronger forward-reachability invariants rather than absence of predecessors.

## Reproduction

- `InfiniteAncestry.lean`: explicit lifted family, natural-valued `Q`, and a real generic-edge chain for arbitrary depth.
- `PeriodicAncestry.lean`: exact quotient `W`, power exponent restricted to `j≡0 (mod 5400)`.
- `GeneralAncestry.lean`: uniform statement for every `m>=1`, including the infinite-target strengthening.
- They import `SheepPowerBridge.lean` from `im-results/agent22-sheep-semantic-bridge/`, which in turn imports Agent 14's `CounterBridge.lean`; source restoration and module conversion are documented there.
- All statements are wholly quantified and require no numerical tests, sampling, untrusted `native_decide`, or external arithmetic oracle. The Lean `#print axioms` commands are included in the files.
- The manually triggered workflow `.github/workflows/agent22-sheep-source-bridge.yml` compiles all three files in the pinned Cryptids environment. The final `arbitrarily_large_exponents_have_deep_chains` theorem is explicitly axiom-audited in [run 41392634957](https://github.com/FlareZ123/bb6/actions/runs/41392634957), with only `[propext, Quot.sound]` and no `sorryAx`.
