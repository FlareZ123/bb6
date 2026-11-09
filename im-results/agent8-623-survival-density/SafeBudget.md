# Digit-path safety budget and ninefold pump for #623

**Agent 8, 9 November 2026.** This note collects original-source all-natural lemmas in [SafeBudgetSource.lean](SafeBudgetSource.lean), together with one explicitly finite root diagnostic. These lemmas do not decide the blank-root machine or BB(6). The earlier complete lossless source transducer is verified in [CI #42562367092](https://github.com/FlareZ123/bb6/actions/runs/42562367092).

## Exact input-specific safety threshold

Define `h(b)` by the total, strictly decreasing ternary recurrence

- `h(0)=0`;
- `h(3q)=max(0,h(q-1)-1)` for `q>0`;
- `h(3q+1)=h(q)+1`;
- `h(3q+2)=h(q+1)+1`.

For every `a,b,d`:

```text
h(b) <= a  ==>  exists A,D. drainB(a,b,d) = some D(A,D).
```

This is an **all-input sufficient condition**, stronger in its dependence on the actual digit path than prior uniform base-three cone bounds. It is not necessary for success, since the source permits a residue-two step when the first counter is zero. The recursive threshold is the exact minimum buffer for the *positive-counter reduction word*, where zero at residue zero remains permitted.

## Source-exact affine horizontal rays

Theorem `drainB_safe_shift`: on `a>=h(b)`, increasing the input first counter by any `t` increases the output first counter by exactly `t`; the output third counter remains **identical**:

```text
drainB(a+t,b,d)
 = Option.map (fun D(A,D) => D(A+t,D)) (drainB(a,b,d)).
```

This extends the repository's older ternary-ones shift threshold to a **per-block carry-sensitive threshold**, using the full original machine, not a copied transition. The proof derives from `digitCode_safe_shift`, by induction on the block count.

## Ninefold self-similarity and infinite safe family

The exact identities

```text
h(9*b+6) = h(b)
drainB(a,9*b+6,d) = drainB(a,b,d+24*b+22)
```

hold for all natural inputs. Define `P(0)=0`, `P(k+1)=9*P(k)+6`. Then `P(k)>=6k` and

```text
h(P(k)) = 0
drainB(0,P(k),d) = some D(0,d+3*P(k)+4*k).
```

Thus an **infinite family of exponentially increasing block counts succeeds with first counter zero**, using exact source machine semantics.

For any `k>=0`, put `b=P(k+1)>=6`. It is even, so the real high-level machine follows the exceptional `a=d+2` branch. A further source theorem proves the exact synthetic two-return escape

```text
highLevelNext(highLevelNext(D(b,b-2)))
  = some D(2+3*b+4*(k+1),7).
```

The displayed composition denotes the option-bind transition and is defined for this family. **These states are synthetic.** There is no proof that the genuine blank-start orbit reaches one.

## Binary family of exponentially many exact safe inputs

The [source proof](BinarySafeSource.lean) extends the first ninefold pump with the genuinely distinct positive-block rule

```text
h(9*b) = h(b)                       (b>0)
drainB(a,9*b,d) = drainB(a,b,d+24*b+2).
```

The two contractions `9*b` and `9*b+6` can be composed in arbitrary finite binary sequences. For a finite Boolean word `w`, define `P([])=6`, `P(false::w)=9*P(w)`, and `P(true::w)=9*P(w)+6`; likewise `C([])=4`, with `C(false::w)=C(w)+2` and `C(true::w)=C(w)+4`. All finite words, with no bound on length, satisfy the exact source identities

```text
h(P(w)) = 0
drainB(0,P(w),d) = some D(0,d+3*P(w)+C(w)).
T(T(D(P(w),P(w)-2))) = some D(2+3*P(w)+C(w),7).
```

The Lean theorem `wordBlock_injective` establishes the encoding is injective. Consequently **each word length n supplies precisely 2^n distinct safe block counts**, all exponentially large in n. This is an infinite two-branch ternary Cantor-like family of individually certified genuine-accelerator returns, extending the one-ray pump. The states remain synthetic; reachability from `D(0,7)` is unproved. The lemmas were compiled independently under source-identical Lean definitions, with standard axioms only; original-source import CI is in progress.

## Outstanding root-specific barrier

The [original-source complete digit decoder](NextDigitSource.lean) allows every original accelerated transition to be checked against the path-specific input requirement `h(b)<=a`, after any necessary `evalA` call. A potentially decisive nonhalting strategy would prove this requirement and evaluator success for every actual blank-origin iterate. No such inductive invariant has been found.

A finite 10,000-state root exploration saw all B-drain entries meeting the safe-budget inequality. The minimum observed slack was zero at index 8, B-input `(2,104)`: the digit path touches first counter zero at `b=12`, residue zero, and completes. This is *diagnostic data only* and must never be treated as an all-time proof.

**Verification:** The exact per-block safety theorem, source-level affine transport, original ninefold pump and singleton diagonal escape passed original-Cryptids source [CI 42563789288](https://github.com/FlareZ123/bb6/actions/runs/42563789288). The second pump and binary family additionally compile in local source-identical Lean 4.36.0-rc2 with only ordinary axioms, and their original-source import is being checked in [CI 42564829678](https://github.com/FlareZ123/bb6/actions/runs/42564829678). Keep them provisionally described until that source job succeeds. Work remains in `im-results/` because external novelty and a genuine blank-root conclusion are unresolved.
