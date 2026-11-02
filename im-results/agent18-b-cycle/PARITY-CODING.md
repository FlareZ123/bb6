# Agent 18: complete parity coding and aperiodicity for the Machine B return map

**Status:** kernel-checked intermediate mathematical theorem, with no claimed Machine B halting decision, BB(6) bound, or independent prior-art novelty. The source is `BParity.lean`, which imports `BReduction.lean`. The directly related machine-level bridge is `Agent18BBridge.lean`.

## The global theorem

For any section state `s=(p,d)` with arbitrary natural coordinates, the return map is

```
F(p,d) = (d mod 2, 3*floor(d/2) + 2 + 4*p).
```

Define `(p_j,d_j)=F^j(s)`. Then for **every** starting state `s`, every starting time `n≥0`, and every proposed positive period `P>0`, it is impossible that `p_{n+j}=p_{n+P+j}` for every `j≥0`.

The exact kernel theorem is

```lean
no_eventual_parity_period (s : Nat × Nat) (n P : Nat) (hp : 0 < P) :
    ¬ (∀ j : Nat,
      (iterF (n+j) s).1 = (iterF (n+P+j) s).1)
```

Thus even a completely arbitrary initial section state yields an **aperiodic** infinite parity-bitstream. In particular the actual Machine B section start `(0,0)` has no ultimately periodic parity word. This does not imply that the very sparse recursively sampled bits `sample n` contain a zero.

## General finite-prefix coding theorem

For any two initial states `s,t` with `s.2≤t.2`, if the first components of `F^j(s)` and `F^j(t)` agree for every `0≤j≤k`, then

```lean
2^k ∣ (t.2-s.2)
```

This is the theorem `coding_divisible`, valid for every natural k, with no finite bounds or machine-specific initial assumptions.

Consequently two states with identical *infinite* parity itineraries have equal second coordinates (`infinite_coding_unique`). The first coordinates are also equal since they are the first parity bit, so the full initial state is uniquely coded by its infinite parity sequence.

## Proof

The transducer has the exact arithmetic identity

```
2*d' + 3*p' = 3*d + 4 + 8*p.
```

If two states agree in both input and output parity, subtracting their equations gives

```
2*(d_t' - d_s') = 3*(d_t-d_s).
```

The difference stays nonnegative whenever the initial payloads are ordered. Inductively, equal first k+1 parity symbols imply that the one-step difference is divisible by `2^k`. The displayed equation gives divisibility of `3*(d_t-d_s)` by `2^(k+1)`; coprimality of 2 and 3 gives divisibility of the initial difference by `2^(k+1)`. Therefore an infinite parity match forces divisibility of a fixed finite difference by arbitrarily high powers of two, which is possible only if that difference is zero.

Finally, `F` strictly increases the second coordinate on every step (`BReduction.F_grows`). If a parity stream were eventually periodic, the two distinct points on the same orbit separated by P steps would have identical entire parity itineraries, contradicting their strictly increasing second coordinates.

## Reproduction and scope

`BParity.lean` compiled with Lean 4.36.0-rc2 using only the shipped `Lean.Elab.Tactic.Omega` through `BReduction.lean`. `#print axioms` reports `[propext, Quot.sound]` for `coding_divisible`, `infinite_coding_unique`, and `no_eventual_parity_period`; there is no `sorryAx`. The manually triggered pinned Cryptids CI workflow also compiles this theorem under Lean 4.35.0-rc4.

This structural result identifies a limitation of finite-period models for the **full** parity word. It does not disprove finite modular descriptions of the different, sparse `sample n` values, so the holdout's halting status stays open.
