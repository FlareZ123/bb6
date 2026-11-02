# A generic, exact, depth-bounded inverse-tree sieve for Sheep

**Scope.** This is an intermediate mathematical result about the already-published one-counter return map of the unresolved six-state Sheep Machine `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`. It establishes a family of **all-time exclusions from the actual blank-entry return state**, assuming the upstream published machine-to-return correspondence. It does **not** resolve the machine's halting status or determine BB(6). The certificate is executable Python with exact integer assertions, not yet a Lean-kernel proof; independent adversarial review remains appropriate.

**Output:** Run `python symbolic_sieve.py` with Python 3.10+ and SymPy (tested with SymPy 1.14). The script reports 252 initial forward return steps, 237 independently validated periods, and a complete modular inverse-tree sieve excluding **3,544 distinct residue classes modulo 5,400** (443/675 of the exponent classes). It covers **every natural exponent** `j` in these classes, with small exponents handled by direct finite-prefix + monotonicity reasoning. SHA-256 of the ascending, comma-separated zero-based excluded residues:

```text
3501152b8f0e5feb4d45fce3505e4457264d2f6001b2ea675508abde300ccb37
```

The class list is generated deterministically from the proof algorithm. There is no forward time horizon on the resulting unreachability conclusion.

## Exact dynamical model and the unresolved obligation

The published Sheep return section starts at `t=5`. For `t=2^a u`, `u` odd:

- if `u=1`, the section halts;
- if `u=3`, `F(t)=3*2^a+a+3`;
- if `u>=5`, `F(t)=2^a*u+a+(u-1)/2`.

Every defined step from `t>=5` strictly increases `t`. The original machine halts precisely if this return orbit visits some `2^j` (via the published original-machine bridge). We certify that specified halting powers can never occur, using a finite *backward* tree whose symbolic nodes each denote infinitely many possible targets.

## Exact symbolic predecessor families

Represent a family of candidate target integers by

```text
Y_f(j) = (2^(j+s) + b)/d,   f=(s,b,d),
```

where `s>=0`, `b` is any integer, and `d>=1` is odd. The root `f=(0,0,1)` is precisely `Y_f(j)=2^j`.

If `x=2^a u` (odd `u>=5`) is a predecessor of `Y_f(j)`, then, by the explicit formula for `F`,

```text
2*Y_f(j) = (2^(a+1)+1)*u + 2a-1.
```

Thus, with `M_a=2^(a+1)+1`, a necessary modular congruence is

```text
2^(j+s+1) = d*(2a-1)-2b     (mod d*M_a).             (1)
```

Solving for `x=2^a u` gives exactly

```text
x = [2^(j+s+a+1) + 2^(a+1)*b + 2^a*d*(1-2a)]/(d*M_a).
```

This is `Y_{parent_a(f)}(j)` with

```text
parent_a(s,b,d)
  = (s+a+1, 2^(a+1)*b + 2^a*d*(1-2a), d*(2^(a+1)+1)).
```

Every *actual* generic predecessor has this form and passes (1). Not every congruence solution necessarily gives an admissible odd `u>=5`: retaining such spurious candidates is **safe** because it only makes closure harder to prove. All produced families preserve `s>=0`, positive odd `d`, and `2^s < 3d`, ensuring the finite exceptional-branch test below is defined.

## Why every node has finitely many possible generic valuations

Let `K_f(a)=d*(2a-1)-2b`, an odd integer because `d` is odd. Modulo `M_a`, powers of two are of the form `±2^r` with `0<=r<=a`, since `2^(a+1)=-1 (mod M_a)`. Therefore there is **no** `n>=0` such that

```text
2^n = K_f(a) (mod M_a)    when  1 < K_f(a) < 2^a.
```

Indeed the positive residues `2^r` are either 1 or even, whereas every negative residue `M_a-2^r` exceeds `2^a`.

The function `generic_tail_bound(f)` searches for an `A` with

```text
1 < K_f(A) < 2^A,      2^A >= 2d.
```

Such an `A` exists for every fixed family because `K_f(a)` grows linearly while `2^a` grows exponentially. Moreover, for all `a>=A` the same inequalities persist:

```text
K_f(a+1) = K_f(a) + 2d,
2^(a+1) = 2*2^a,      2^a >= 2d.
```

Consequently all possible generic-parent valuations are in the **explicit finite set** `a=0,...,A-1`.

## Exhausting all exponents in one residue class

For a fixed symbolic node `f`, a candidate valuation `a<A`, and `j ≡ r (mod 5400)`, equation (1) must hold modulo the positive odd integer `m=d*M_a`.

The script obtains an integer `p` using SymPy's multiplicative-order routine, then **checks `pow(2,p,m)==1` by exact Python arithmetic**. This assertion, not any unverified claim of minimality from SymPy, is the certificate that `p` is a genuine period.

As `j=r+5400*k` varies over all nonnegative `k`, the residue of `2^(j+s+1)` is exhausted exactly by

```text
k=0,...,p/gcd(p,5400)-1.
```

A candidate valuation is retained if *any* of these finitely many checks passes; otherwise it is mathematically impossible for **every** exponent in that class.

## Closing the exceptional u=3 branch uniformly

We must also eliminate a predecessor `x=3*2^a`, which would require

```text
2^(j+s)+b = d*(3*2^a+a+3).                          (2)
```

Define `h=floor(log2(3d))-s`. Every generated family has `h>=0`, and the positive integers `L=3d-2^(s+h)`, `U=2^(s+h+1)-3d` are strictly positive (as `3d` is odd). Split all valuations into `a>=j-h` and `a<=j-h-1`, for `j>=h+1`.

The first case is impossible whenever

```text
L*2^j > 2^h*b,                                      (3)
```

since `d*3*2^a >= 3d*2^(j-h) > 2^(j+s)+b`.

The second case is impossible whenever

```text
U*2^j > 2^(h+1)*(d*(j+3)-b),                         (4)
```

because `3d*2^a <= 3d*2^(j-h-1)` and `a+3 <= j+3`.

The script finds a threshold `J` satisfying (3), (4), and

```text
U*2^J > 2^(h+1)*d.                                  (5)
```

All these strict inequalities then persist for every `j>=J`: the exponential terms double, while the only variable linear term grows by `d`; (5) ensures (4) remains strict under induction. The check `J<=100` is enforced for **every node actually explored**. Thus no node can have a hidden special-branch predecessor when `j>=100`.

## Recursion and the starting-state exclusion

For each `r`, `inverse_tree_closes(f,r,depth)` computes all possible generic-parent valuations after eliminating the special branch. If none exists, `Y_f(j)` has no predecessor at any `j>=100` in that residue class, and the family is closed.

Otherwise, if `depth>0`, the routine recursively requires closure of *every* possible parent family. At each visited node it checks

```text
2^(100+s)+b > 5d,
```

hence `Y_f(j)>5` for all `j>=100`. In a forward orbit from `5`, any visited state strictly larger than `5` has a previous section state; recursively closing all its possible predecessors contradicts first arrival. Induction on the chosen finite backward-tree depth proves soundness. `False` means merely **not certified at this depth**; it does not assert reachability.

The root uses `depth=3`, allowing three successive generic-parent expansions after the first target and a fourth generation of no-parent leaves. It yields 3,544 closed classes modulo 5,400 with all assertions passing.

The remaining exponents `j<100` are handled separately: an exact forward computation from `5` stays defined and non-halting for 252 steps and finishes at `t>2^99`. Since `F(t)>t` whenever defined from `t>=5`, no smaller power can ever be encountered afterward. This finite check plus monotone-growth argument proves exclusion of all small exponents for the actual return trajectory.

## Evidence boundary and next decisive obligation

This is a new (within our shared repository) **general-purpose inverse-tree certificate engine** rather than a hand-optimized modular case table. It reproduces and surpasses several previous fixed-depth families, but a finite backward-depth certificate cannot by itself exclude arbitrary remaining exponent classes. In particular, the other 1,856 classes modulo 5,400 are **unresolved by this method**.

To settle the Sheep holdout, one must cover all possible halting-target exponents, perhaps through a uniform invariant for arbitrarily deep inverse branches, an infinite-state regular representation of ancestry, or a different forward-orbit induction. A future independent Lean formalization should certify the generic-tail lemma, finite-period checking, exceptional-branch threshold, and tree recursion, then connect them to DeepMind's formal high-level state/return predicates at a pinned revision. No claim is made that these intermediate exclusions are a new externally published discovery or that BB(6) has been determined.
