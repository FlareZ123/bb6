# Branch-10 q=0 inverse block and its 2-adic depth parameter

**Status:** exact algebraic derivation; not yet formalized in Lean. This is a structural result about the inverse-candidate tree, not a nonreachability theorem. In particular, the F sibling at each S split remains a separate candidate and must not be silently discarded.

## Inverse maps and a useful coordinate

For an odd state `(a,b)), the two inverse candidates are

```
F(a,b) = ((a-3)/2, b+a)
S(a,b) = ((4a+b-26)/4, (b+4)/2)   [only when b = 2 mod 4].
```

For a positive-even state, the inverse candidate is

```
E(a,b) = ((4a+b-14)/4, b/2)      [with b = 2 mod 4].
```

Set

```
z = b-a-9,       R = 2a+b.
```

Thus `b=a+z+9` and `R=3a+z+9`.

## Exact FSFE block

Suppose

- `a >= 29`,
- `a = 1 (mod 4)`,
- `z >= 15`,
- `z = 15 (mod 16)`.

Then the inverse-candidate branch F, S, F, E is legal. The intermediate states are exactly

```
F:  a1 = (a-3)/2,             b1 = 2a+z+9
S:  a2 = a+(z-23)/4,          b2 = a+(z+13)/2
F:  a3 = (4a+z-35)/8,          b3 = 2a+(3z+3)/4
E:  a4 = a+(5z-123)/16,        b4 = a+(3z+3)/8.
```

The hypotheses make every displayed division integral and give the required parity and lower bounds at each step:

- `a1 >= 13`, `a1` odd, and `b1 = 2 (mod 4)`;
- `a2 >= 13` and `a2 = 3 (mod 4)`;
- `a3 >= 6`, `a3` even, and `b3 = 2 (mod 4)`.

For the output pair `(a',b')=(a4,b4)`, direct simplification gives

```
z' = b'-a'-9 = (z-15)/16,
R' = 2a'+b' = R-24.
```

Equivalently, one block divides `z+1` by 16 and decreases the rank `R` by exactly 24.

This is a statement about an available inverse branch. Since `odd_back` gives a disjunction at the S node, it does **not** imply that the S child is the reachable predecessor; the competing F child must still be discharged separately.

## Iteration

If `z+1` is divisible by `16^m` and `a >= 29+3m`, the FSFE branch can be iterated `m` times.

Writing `(a_k,b_k)` for the state after `k` blocks and `z_k=b_k-a_k-9`, the exact identities are

```
z_k+1 = (z+1)/16^k,
R_k   = R-24k,
a_k   = a + ((z+1)-(z_k+1))/3 - 8k.
```

For validity, note that each block has increment
`a_{k+1}-a_k=(5z_k-123)/16 >= -3` when `z_k>=15`. Hence `a_k>=a-3k`. Before every non-final block, `z_k+1` is divisible by 256, so `z_k=255 (mod 256)`; this makes `a_{k+1}=a_k (mod 4)`. Thus the required `a_k=1 (mod 4)` persists through all blocks. The final block needs only `z_k=15 (mod 16)`.

Consequently the number of consecutive FSFE blocks on this branch is controlled by the 2-adic order of `z+1`, not by a fixed depth.

## Application to the branch-10 q=0 seed

For `d=7` and `n=23+32u`, the last-reset prestate is

```
a = 2^n(d+6) + (2d-3n-21)/4
  = 13*2^n - 24u - 19,
b = 2(a-d)+1 = 2a-13.
```

Therefore

```
z+1 = b-a-8 = a-21
    = 13*2^n - 8(3u+5).
```

Since `3u+5 < 2^(n-3)`, the two terms have different 2-adic orders, and

```
v2(z+1) = 3 + v2(3u+5).
```

So the FSFE branch has length

```
4 * floor((3+v2(3u+5))/4)
```

before this particular repeated block condition stops. The valuation `v2(3u+5)` is unbounded over natural `u`: for each `k`, the congruence `3u+5 = 0 (mod 2^k)` has a natural solution because 3 is invertible modulo `2^k`.

Examples:

- `u=0` gives `v2(3u+5)=0`, so this block does not occur; this is the concrete `(n,d)=(23,7)` tree already recorded in `BB429Q0Row237.lean`.
- `u=425` gives `3u+5=1280=2^8*5`, hence two consecutive FSFE blocks. This corresponds to `n=13623`.

## Research consequence

A fixed-depth inverse-certificate search cannot uniformly close this q=0 family while retaining the FSFE branch: there are natural parameters with arbitrarily many consecutive blocks. The useful next step is a parameterized argument on `v2(3u+5)` (or a root invariant that excludes the side branches before the block repeats), not simply increasing a fixed inverse-depth cap.

The exact finite q=0 proof for `(n,d)=(23,7)` remains valid only for that concrete seed until the parameter family is formally handled. This block calculation does not extend it to all `u` and does not decide machine #429 or BB(6).


## Root-compatibility correction: syntactic versus reachable block count

The formula above
```
4 * floor(v2(z+1)/4)
```
counts **syntactically available** F,S,F,E inverse candidates, based only on divisibility by 16. It is not the number of blocks that can occur on a genuine blank-root path.

There is a stronger all-time invariant at the intermediate positive-even state P3. In the w=z+1 coordinate,
```
P3.second = 2*a + 3*w/4.
```
If a=1 (mod 4) and 16 divides w, then
```
P3.second = 2 (mod 8)  iff  v2(w) >= 5;
P3.second = 6 (mod 8)  iff  v2(w) = 4.
```
Since P3.first is positive even, a genuine root path requires P3.second=2 (mod 8). Therefore a completed root-compatible block requires valuation at least 5, not merely 4.

If v=v2(w0), the maximum number of completed root-compatible blocks along this one branch is consequently
```
floor((v-1)/4),
```
leaving residual valuation in {1,2,3,4}. For residual 4, the next syntactic F,S,F prefix reaches a positive-even P3 with second coordinate 6 mod 8 and is immediately impossible. Residuals 1,2,3 have different partial inverse grammars and are not closed by this observation.

This correction is important for the q0 family: when u=9 (mod 16), v=3+v2(3u+5) is unbounded, but the root-compatible completed-block count is floor((v-1)/4), not floor(v/4). For u=3 (mod 16), v=4: one full block is syntactically integral, but its P3 is root-incompatible, so it contributes **zero** completed root-compatible blocks.

The competing F sibling at every S split remains a separate obligation in either count. This correction is a branch-level necessary-condition result, not a q0-family nonreachability theorem.
