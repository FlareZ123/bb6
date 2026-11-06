# Machine C deep affine stopping inputs: exponential residual barrier

**Status:** A complete paper proof from the exact checked-in section stopping and affine-scale equations, awaiting independent Lean kernel certification as a combined theorem. The original-source prerequisite equations are separately certified in the Machine C source chain. This is a bound for *hypothetical stopping inputs*, not a blanket exclusion or a halt/nonhalt decision of Machine C or BB(6).

## Theorem

Let natural numbers `j,m,k,d,Y` satisfy

```
m >= 1, m odd,
k+j+3*m+5 = 2^(2*m+2) * (j+3),
2^d * (Y+2) = k+2.
```

Then

```
Y >= 2^(m+2) - 6*m - 1.
```

The statement is meaningful independently of the initial section's parity. For the source-certified *deep affine sector*, `Y` is precisely the genuine `BB6.Agent15.affineNormalize (2*j+3) k` residual right counter and `d=BB6.Agent15.oddDepth k`. In the genuine sector, existing `DeepSecondFinal.lean` also requires `Y>=4` and `Y%12=4`. For `m=3`, the new numeric lower bound is 13; it grows exponentially with odd `m`, in contrast to a fixed lower bound of 4.

This rules out residual right counter four for every odd `m>=3` under the exact stopping equation. It does **not** settle source reachability for any residual right counter above the bound.

## Proof

Write `L=m+1`. Since `m` is odd, `L` is positive even. Set

```
B = (2^L-1)/3,  A = 2^L+1,  Q = A*B = (2^(2*L)-1)/3.
```

Here `B` is a positive odd integer, `2^L=3B+1`, and `m≤B<A`. To verify every size/parity assertion, write `m=2r+1` and `B_r=(2^(2r+2)-1)/3`. Direct algebra gives `B_0=1` and `B_(r+1)=4B_r+1`. Induction makes every `B_r` positive and odd; it also proves `B_r≥2r+1`, because `4B_r+1≥4(2r+1)+1≥2(r+1)+1`. Finally `A=3B+2>B≥m`.

From the stopping equation,

```
k+2 = (2^(2*L)-1)*(j+3) - 3*m.
```

Because `2^(2L)-1` is divisible by three, the scale equation implies `3 | 2^d*(Y+2)`. Since powers of two are coprime to three, write `Y+2=3*v` for a **positive** integer `v`. Dividing the stopping equation by three gives the exact equality

```
v*2^d + m = Q*(j+3).                (1)
```

It is enough to show `v+2*m > 2*B`. Suppose contrariwise `v+2*m <= 2*B`.

The identity `2^(2L) = 3Q+1` lets us replace `d` by the residue `t=d mod (2L)` when applying (1) modulo `Q`.

**Case `0 <= t < L`.** Since `v <= 2B-2m`,

```
0 < v*2^t+m <= (2B-2m)*2^(L-1)+m
             <= B*2^L+m < B*(2^L+1) = Q,
```

where the last strict inequality can be seen directly from `m<=B` (true for `m>=1` odd), with a stronger negative term in the preceding expression. This contradicts `Q | v*2^t+m`.

**Case `L <= t < 2L`.** Put `r=t-L`, so `0 <= r < L`, and `s=v*2^r`. Modulo `A`, the identity `2^L=A-1` gives `s ≡ m (mod A)`. Since `0 < m < A`, some integer `u>=0` satisfies

```
s = m+u*A.                          (2)
```

Modulo `B`, the identity `2^L=3B+1` gives `B | s+m = u*A+2m`, and `A=3B+2`, hence `B | 2*(u+m)`. As `B` is odd, `B | u+m`, which is a positive integer. Thus `u+m>=B`.

At the same time, (2) and `r<L` imply

```
u*2^L < m+u*A = s = v*2^r <= v*2^(L-1).
```

Therefore `2u<v`, and `v+2m>2(u+m)>=2B`, contrary to the assumption.

Both cases prove `v+2m>2B`. Since these are integers,

```
Y = 3*v-2 >= 3*(2B-2m+1)-2
            = 6B-6m+1
            = 2^(m+2)-6m-1.
```

This completes the paper proof.

## Source chain, reproducibility and limits

The exact second-family equation is the original Machine C stopping identity in `im-results/agent15-c-halting/`. The affine-scale equation `2^d(Y+2)=k+2` is `normalize_three_depth_invariants` in `AffineParityDepth.lean`, imported by the genuine-root theorem `second_halt_deep_sector` in `SecondDeepSector.lean`. The factor-three lemma and real residual `Y%12=4` are `ModThree.lean` and `DeepSecondFinal.lean`, respectively; both were compiled successfully before the later failure in original-source CI 42194394835. This new exponential theorem itself has **not yet** been represented as a kernel-checked Lean theorem.

Numerical checks of the exact source normalization at even `j` with `(j+m)%4=3` for `m=1,3,5,7,9,11`, sampling `j<200000`, found no violations. Minimum observed residuals for those depths were `4,220,508,45052,327676,16252924`; these are illustrations, not part of the proof. The proof quantifies over every natural stopping parameter and every valid affine-scale exponent.

The next valuable application is to combine this depth-dependent obstruction with exact source inverse ancestors of the surviving residuals. It remains unknown whether any stopping input is reached from the authentic blank section at all.
