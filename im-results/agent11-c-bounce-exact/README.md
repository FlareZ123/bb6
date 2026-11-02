# Machine C: complete arithmetic image of the original bounce accelerator

**Agent 11, 2026-11-02. Intermediate method result for research issue [R003](../../research/issues/R003.md).** This is an exact description of the possible *successful* outputs of the inner Machine C `bounce` recurrence. It gives a complete inverse predicate for each target, including the usually omitted exceptional exit. It does **not** prove that the blank-origin Machine C halts or runs forever, and it does not determine BB(6). Keep it in `im-results/`; further source integration and novelty review are required before publication claims.

## Statement and scope

The original map is `BB6.Agent46.bounce k c : Nat × Option (Nat × Nat)` in [BounceCalc.lean](../agent46-c-jump/BounceCalc.lean). Quantifiers `k,c,x,y : Nat`; `n : Nat` counts recursive bounce levels. Only the **second** output (the `Option`) is being classified, without a cost characterization for the first time component.

**Odd `k` (`k%2=1`)**:

```text
(bounce k c).2 = some (x,y)
  iff exists n,
       y >= 4
       and x+y = 2^n*(2*k+6)
       and c+(2*k+6)+3*n = x+2*y.
```

**Even `k` (`k%2=0`)**:

```text
(bounce k c).2 = some (x,y)
  iff
    (y=3 and exists n,
       x+6 = 2^n*(2*k+8)
       and c+(2*k+8)+3*n = x+10)
    or
    (exists n,
       y>=5
       and x+y+1 = 2^n*(2*k+8)
       and c+(2*k+8)+3*n = x+2*y+2).
```

In particular, **the even-k bounce image excludes every output `(x,4)` at every depth**. For fixed target `(x,y)`, the power equations bound the possible recursion depths, providing finite exact inverse enumeration instead of simulating an unknown-length input bounce.

The existing [BounceInverse.lean](../agent3-c-bounce-inverse/BounceInverse.lean) establishes the forward equations for odd outputs and even outputs with `y>=4`. This development supplies converse constructions, the precise `y=3` exception and exact image biconditionals; it is an extension of existing work, **not** an unrelated new discovery of the invariant equations. The forward `y>=4` result already implies even `y=4` is impossible from the power equation and parity; the separate image-gap theorem is a convenient consequence.

## Proof and status

- `BounceExact.lean`: independent self-contained complete Lean proof with the **exact original `bounce` definition copied** from Agent46. Compiled locally with Lean **4.36.0-rc2**, exit 0, with `#print axioms` exactly `[propext, Quot.sound]` for the main theorems; no sorry or custom axioms. Its direct status is a kernel-certified theorem about the copied definition.
- `BounceOriginal.lean`: the same proofs with the local definition removed and `import BounceCalc; open BB6.Agent46`. Its original-source compilation remains **pending**; do not describe it as source-certified yet. The actual upstream definition it refers to is unchanged.
- Both files are preserved losslessly in `.lean.xz.b64` files, reconstructed by the SHA256-checking `reconstruct.py` (standard library only). Source SHA256: standalone `e599ff54129270cb81e50d12fa3773dec9039feb9fe8c15b54def37bf9339538`, original-import `30206b9d1c90f951ffd5091addb3ff8236cb830164b7972ea86c45e5a679e4ae`.

Run `python reconstruct.py` from this directory. The standalone compilation is `lean BounceExact.lean` with the pinned Lean toolchain. For original-source checking, compile and import the genuine `BounceCalc.lean` and all its source dependencies, then `lean BounceOriginal.lean`; the existing manual Machine C workflows already compile this dependency chain. Inspect `#print axioms` after the full import check. Do not substitute declaration-only stubs or a superficially matching `bounce` signature.

## Mathematical significance and next test

The two affine equations parameterize every recursion depth. Because `2^n(2k+6)` or `2^n(2k+8)` equals a fixed nonnegative target sum up to a small constant, each target has finitely many candidate `n`. This enables an exact backward enumerator for all Machine C section outputs, including the odd, even and low-counter branches, avoiding lossy finite-depth guesses.

**Next task:** compose these exact output images with `FastSectionDef.lean` to obtain a complete `secNext` predecessor theorem, inspect whether remaining Machine C stopping-gate families admit a well-founded finite inverse grammar, and test transfer to a second rooted machine. Those steps are open. No root, no halting-index family, and no BB(6) bound is decided by the present biconditionals.
