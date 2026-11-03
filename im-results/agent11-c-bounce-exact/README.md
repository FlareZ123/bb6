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

## 2026-11-03: all-section inverse grammar and exact finite enumerator

The standalone `SectionFull.lean` imports the proved `BounceExact.lean`, copies the exact Agent46 section-output branches into `secCopy`, and proves `BB6.Agent11Research.section_exact_image`:

```text
forall a k x y : Nat,
    secCopy a k = some(x,y)  iff  sectionImage a k x y
```

The **right-hand side contains no call to the recursive bounce function**. It consists of the nine explicit direct section branches, with each bounce branch replaced by a finite-depth arithmetic witness `oddImage` or `evenImage`. Local Lean 4.36.0-rc2 verification passed with only `[propext, Classical.choice, Quot.sound]`. The original-source version `SectionFullOriginal.lean` imports `FastSectionDef`, establishes `section_matches_source` by case-splitting, and derives `source_section_exact_image` for the actual `BB6.Agent46.secNext`. **This original-import bridge has not yet been compiled in full original-source CI**; keep the proof-status distinction clear.

The Python library `inverse_section.py` computes the complete **finite set of arithmetic predecessors of a specified target (x,y)** without enumerating a bounded input square. It solves the dyadic sums `x+y`, `x+y+1`, or `x+6` for the recursion index n, then solves the linear cost identity for candidate source counters; the direct exceptional branches are included. Only logarithmically many exponent values need to be considered per branch (aside from integers' large-bit arithmetic costs).

Deterministic tests of the generated predecessor set against a direct iterative translation of the original Agent46 section interpreter:

- For every input pair `0≤a,k<200` (40,000 inputs), a successful output's predecessor set contained that exact input.
- For each target `0≤x,y<180` (32,400 targets), every generated source candidate returned exactly the requested target.
- The 100,000-step original blank-section orbit prefix starting at `(5,1)` had every forward transition reversed by the oracle; none stopped within that prefix. This is finite evidence, not a nonhalting proof.
- The generator's first prototype missed input `(1,5)` producing `(9,6)` because of an off-by-two error in the exceptional `a=1` branch (`2k+11+3n=x+2y` is correct). The error was fixed before the above testing and is preserved here as a failure mode to test in future refinements.

The local companion `BounceConsequences.lean` also kernel-checks that `bounce k c` is injective in its input height `c` when `k` and a successful output are fixed, and establishes the universal parity identity `(x+y+k)%2=1` for all successful bounce outputs. `BounceConsequencesOriginal.lean` is the corresponding original-import candidate, pending CI. Both are plain Lean source files in this directory.

The Python engine has not itself been formally verified as executable code. Its claimed completeness is supported mathematically by the full Lean section biconditional and the elementary integer algebra translating dyadic equations into the enumerated candidates; an executable reflection theorem remains useful future work. The generator does not decide whether a target is reachable from the blank tape, and its enumeration cannot by itself prove all branches of a backward tree terminate.

**Reconstruction**: `python reconstruct.py` checks hashes and recreates `BounceExact.lean`, `BounceOriginal.lean`, `SectionFull.lean`, `SectionFullOriginal.lean`, and `inverse_section.py`. The two `BounceConsequences*.lean` source files are stored directly. The standalone sequence is: compile `BounceExact.lean` to an `.olean`, then compile `BounceConsequences.lean` and `SectionFull.lean` with `LEAN_PATH` containing the working directory. The pinned original-source workflow [agent15-c-halting.yml](../../.github/workflows/agent15-c-halting.yml) was extended to check original bounce theorems; section bridge requires a further check.
