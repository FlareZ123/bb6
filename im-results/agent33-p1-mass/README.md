# Exact mass accounting and logarithmic depth bound for the authentic P1 G drain

Agent 33, 2026-11-02. **Intermediate reusable structural theorem**, not a P1 halting decision, BB(6) bound, or universally optimal runtime theorem. Original formal source: `im-results/agent1-p1-map/PosEvenForm.lean`, which copies the published Google DeepMind accelerator `G`; its full unmodified file is compiled in the manual CI verification.

## Definitions and exact all-input identity

The original recursive P1 operation `G(k,c)` has a low branch when `c<2k`, replacing `(k,c)` by `(k-(c/2+1), 2c+3)`, a medium boundary exit when `2k≤c≤2k+1`, and a high exit otherwise. There are no parity or forward-reachability assumptions in this analysis.

Define `depth(k,c)` as the exact number of low recursive `G` calls, and `extra(k,c)` by the source-matched recursion:

- on a low branch, add `1+(c%2)` and recurse;
- on a medium boundary exit, use `1+(c%2)`;
- on a high exit, use zero.

The Lean theorem `BB6.Mass.G_mass_exact` proves for every natural `k,c`:

```text
G(k,c).fst + G(k,c).snd = 2*k + c + 2 + extra(k,c).
```

This refines Agent 1's prior source-verified `G_mass_lower` inequality into an exact recursive accounting of the positive rank increment. The theorem uses only standard axioms `[propext, Quot.sound]`, no `sorryAx`.

## Exponential recursion-depth certificate

The key quantitative result is `BB6.Mass.depth_power_bound`:

```lean
(k c : Nat) (hpos : 0<depth k c) :
  2^(depth k c - 1)*(c+3) ≤ 2*k+2
```

It is proved by strong induction on k. On a low branch the right counter changes from c to `2c+3`, so the expression `c+3` **doubles exactly**, while the first argument strictly decreases. If the child has further recursive calls, transport its bound; if the child is terminal, the parent's low guard `c<2k` yields the bound immediately. Thus for d>0 one also has `3*2^(d-1)≤2k+2`. This gives a logarithmic depth bound even for c=0, the slowest initial counter.

The consequent Lean theorem `depth_le_log` holds for every k,c:

```text
depth(k,c) ≤ Nat.log2(2*k+2) + 1.
```

Here `Nat.log2` is the integer binary logarithm. The proof uses Std's exact `Nat.le_log2` theorem.

## Global logarithmic mass envelope

Every low branch contributes at most two extra mass units, and the final branch contributes at most two. Lean theorem `extra_le_depth`:

```text
extra(k,c) ≤ 2*depth(k,c)+2.
```

Combining these bounds with the exact mass identity yields the fully source-level theorem `BB6.Mass.G_mass_log_bound`:

```text
G(k,c).fst + G(k,c).snd
  ≤ 2*k+c+6+2*Nat.log2(2*k+2).
```

The input-to-output sum surplus of `G` above its naive weighted input `2k+c` is therefore at most additive **O(log k)**. This is an all-input, no-simulation property, and should be useful for rank-gap estimates, bounding recursion in inverse searches, and rigorous complexity envelopes.

## Verification and provenance

- Source archive `GMass.lean.xz.b64`: unpacked Lean source SHA-256 `e8026c51bc747bfc6108600d720e402a04718e2b9c6adbc2547464ce6f3f60bf`.
- Restore via XZ decompression after Base64 decoding. The manual workflow `.github/workflows/agent33-p1-g-mass.yml` checks this SHA-256 and imports the **unmodified** original `im-results/agent1-p1-map/PosEvenForm.lean` under Lean 4.36.0-rc2.
- Original-source verification: first successful [run 41434283232](https://github.com/FlareZ123/bb6/actions/runs/41434283232) compiled the exact identity and exponential bound. The *expanded log-theorem* verification is the next manually dispatched run; use workflow history for its final status before claiming source-level success.
- Local Lean 4.36.0-rc2 compiles all seven theorems, with `#print axioms` reporting only `[propext, Quot.sound]` and no admitted proof.

This formalizes an elementary structural property in a machine-specific reusable form. External novelty has not been established. Neither the rank envelope nor the depth bound implies blank-tape nonhalting or a universal limit on the number of accelerated P1 steps; the final halting criterion remains unresolved.
