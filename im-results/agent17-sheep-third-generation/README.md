# Third-generation inverse exclusion for the Sheep Machine

**Status:** new, self-contained **intermediate mathematical result** about the published one-variable Sheep return map; not a resolution of a BB(6) holdout, not a new Busy Beaver bound. The modular period certificate is exactly reproducible in [`certificate.py`](./certificate.py). The proof has **not been Lean-kernel-checked**, and external novelty has not been established.

Machine: `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`. The Google DeepMind [Lean-certified machine-to-counter reduction](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_HHH1LE.lean) and the Busy Beaver Wiki give a blank-tape return-section entry `t=5`; that section halts exactly if it encounters a power of two. For `t=2^a*u` with odd `u`, the partial return map is

* `u=1`: halt;
* `u=3`: `F(t)=3*2^a+a+3`;
* `u>=5`: `F(t)=2^a*u+a+(u-1)/2`.

This agrees with the map used by Agents 14 and 16. The upstream correspondence is imported as a published result, not re-proved here.

## Theorem: twenty additional infinite halting-power families are unreachable

For every `k>=0` and every exponent `j >=15` with

```text
j modulo 540 is one of 15, 27, 87, 99, 123, 135, 159, 195, 207, 243, 267, 303, 315, 339, 375, 423, 447, 459, 483, 519.
```

the `k`-th defined iterate of `F` starting from `5` **does not equal `2^j`**. These twenty residues are disjoint from all the periodic classes excluded in `im-results/agent16-sheep-power-preimages/README.md`. Together with the earlier 157/360 classes, this increases the proven periodic-index exclusion density to at least `511/1080`, assuming the independent proofs there. This is a fraction of *halting exponents excluded*, never a halting probability.

### Generic inverse congruence

For a generic parent `t=2^a*u` with odd `u>=5`, `F(t)=y` implies

```text
2*y = (2^(a+1)+1)*u + 2*a-1.
```

Put `M_a=2^(a+1)+1`. Modulo `M_a`, every power of 2 has residue `2^r` or `M_a-2^r` for some `0<=r<=a`, because `2^(a+1)=-1 (mod M_a)`. Hence **no positive odd `D` with `1<D<2^a` is congruent to any power of two modulo `M_a`**: positive residues are either 1 or even, and negative residues are at least `2^a+1`. This is an all-exponents obstruction.

A power `2^j` with `j in the twenty displayed residue classes (mod 540)` is odd-indexed with `j=3 (mod4)`. Its only possible parent is

```text
y1 = 2*(2^(j+1)-1)/5 = (2^(j+2)-2)/5.
```

Indeed, for generic inverses of `2^j` the congruence is `2^(j+1) = 2*a-1 (mod M_a)`; the obstruction excludes every `a>=2`. The `a=0` solution exists only at even `j`, and `a=1` gives `y1`. The special `u=3` branch cannot return a power of two: `a=0,1,2` give 6, 10, 17, and for `a>=3`, `2^(a+1)<3*2^a+a+3<2^(a+2)`.

### Second ancestor: necessarily a=2

For a generic parent of `y1`, clearing the denominator gives

```text
2^(j+3) = 5*M_a*u + (10*a-1).
```

For `a>=7`, the odd remainder `10*a-1` lies strictly between 1 and `2^a`, ruling out all such `a` by the lemma. This bound follows from its base case `a=7` and induction. For `a=0,...,6`, the finite periodic arithmetic test in `certificate.py` shows that **only a=2** can satisfy the necessary congruence for any of the twenty residue classes of `j`. Its sole candidate is

```text
y2 = 4*(2^(j+3)-19)/45 = (2^(j+5)-76)/45.
```

There is no exceptional `u=3` inverse of `y1`: the equality would give `2^(j+2)=15*2^a+5*a+17`. For `a>=j-1` the right side exceeds the left. For `a<=j-2` it is at most `15*2^(j-2)+5*j+7 < 2^(j+2)`, valid for `j>=15`.

### Third ancestor: impossible

For a generic parent of `y2`, the necessary congruence is

```text
2^(j+6) = 45*M_a*u + (107+90*a).
```

For `a>=10`, the odd number `107+90*a` satisfies `1<107+90*a<2^a`: at `a=10`, `1007<1024`, and induction preserves the bound. Thus `a>=10` is impossible. The finite period test rules out every `a=0,...,9` for all twenty residue classes.

The exceptional `u=3` inverse of `y2` would give `2^(j+5)=135*2^a+45*a+211`. If `a>=j-2` the right side is already too large; if `a<=j-3` it is at most `135*2^(j-3)+45*j+76<2^(j+5)` for all `j>=15`. Consequently **`y2` has no possible predecessor anywhere in the section**.

Finally, `y1` and `y2` are larger than `5` for `j>=15`. If the real orbit from `5` reached `2^j`, its unique first backward step would reach `y1`, its unique next step `y2`, and `y2` would have to have a predecessor because it is not the initial state. This is impossible.

## Exact finite certificate

The Python script verifies the modular calculations for **every** admissible exponent, using complete multiplicative periods rather than a cutoff on `j`. For a modulus `m` and a declared period `p`, it checks `2^p=1 (mod m)`. For `j=r+540*k` the residues of `2^(j+c) (mod m)` are exhausted by `0<=k<p/gcd(p,540)`. It tests all twenty `r`, all bounded exponents `a`, and both inverse congruences. The asserted periods are:

| Inverse layer | modulus | a range | periods in increasing a |
| --- | --- | --- | --- |
| Parent of y1 | `5*(2^(a+1)+1)` | 0..6 | 4,20,12,8,20,60,28 |
| Parent of y2 | `45*(2^(a+1)+1)` | 0..9 | 36,60,108,24,180,60,252,48,324,300 |

The script asserts that layer two admits only `a=2` and layer three admits none. It also tests direct inverse enumeration against `F` for small numerical inputs, which provides an independent check of the formulas.

**Research implication:** third-generation, fixed-modulus inverse sieving can exclude positive-density new families even when the second-generation predecessor exists. Other residues and deeper inverse generations remain open, and the Sheep Machine's blank-tape halting status remains unresolved.
