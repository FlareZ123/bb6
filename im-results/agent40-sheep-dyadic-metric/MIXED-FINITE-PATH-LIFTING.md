# Every finite generic Sheep quotient walk has one real integer realization: all even moduli

**Agent 40, 7 November 2026. Intermediate all-parameter paper theorem.** Let `m=2^p q`, with `p>=1` and odd `q>=1`. For the **generic synthetic first-even Sheep return graph** on even residues modulo m, **every finite directed walk** of arbitrary length is realized by consecutive genuine generic first-even returns of a **single positive integer**, with the integer chosen freely and arbitrarily large. The successful starts contain a whole eventual arithmetic progression of positive density. This theorem extends [the dyadic finite-path proof](FINITE-PATH-LIFTING.md) to *every* odd cofactor q, including q divisible by 3 or 5, and strengthens the earlier [all-modulus coherent pairwise mixing theorem](../agent22-sheep-mixed-hub/COHERENT-ORBIT.md). The claimed path may revisit zero residue or contain long odd runs. **No statement is made about the one fixed authentic blank-even Sheep source 10**; neither Sheep nor BB(6) is decided.

## Definitions and theorem

Let `G_m` be the directed graph whose vertices are the even residue classes modulo m. Put an edge `r->s` exactly when there exists **some** positive even generic Sheep section source `x=2^a u`, with `a>=1` and odd `u>=5`, such that its true first-even return `E(x)` is defined and nonterminal, its intervening odd part is >=5, and `x≡r`, `E(x)≡s (mod m)`. Thus edges have authentic witnesses, though different edges may initially use different ones. The published map is

```
F(x) = x+a+(u-1)/2,
F(x)-1 = 2^h v, with v odd >=5,
E(x) = 1+3^h v.
```

These one-variable returns are connected to the original six-state machine by [Agent16's source-checked semantic bridge](../agent16-sheep-even-return/README.md), original-source [CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547). We never interpret an arbitrary section start as the machine's fixed genuine blank start.

**Theorem (all-even-modulus finite-path realization).** Given any finite directed walk `r_0->r_1->...->r_n` in `G_m`, any N, and a choice of generic integer edge witnesses with branch parameters `(a_i,h_i)` for every edge, let `c_i=a_i+h_i+1`, `C=sum_i c_i`, `P=p+C`. There exists a residue `x_star mod 2^P*q` such that **every sufficiently large positive integer**

`x=x_star+2^P*q*t`

follows n consecutive actual generic, nonterminal first-even returns with `E^i(x)≡r_i (mod m)` for every `i=0,...,n`, and exact branch letters `(a_i,h_i)`. The starts can exceed N, and the final value increases by precisely `A*2^p*q` under one period shift, where

`A=product_i [3^(h_i)*(1+2^(a_i+1))]` (odd).

Consequently the actual path-realizing starts have lower asymptotic density at least `1/(2^P*q)` among positive integers, and conditional lower density at least `2^(-C)` among positive integers in the initial source residue class `r_0 mod m`. All quantifiers include *every* even modulus, every finite genuine-edge path, and every finite length n. If n=0, choose any sufficiently large x in the initial even residue class.

## The two exact branch congruences

Fix a generic branch letter `(a,h)`, its cost `c=a+h+1`, and put `D=1+2^(a+1)` (odd). At any binary precision `Q>=c+1`, and even target residue y modulo `2^(Q-c)`, define

```
T[Q,a,h](y)
  = 2^a * D^(-1) *
    [3-2a + 2^(h+1)*3^(-h)*(y-1)]   (mod 2^Q).
```

All inverse factors exist modulo powers of two. This parent has exact valuation a, and for any sufficiently large positive x in the corresponding binary residue class, `E(x)≡y mod2^(Q-c)` with **exact** h. Indeed `2(F(x)-1)=D*u+2a-3`, and the inverse congruence yields

`D*u+2a-3 ≡ 2^(h+1)*3^(-h)*(y-1) (mod2^(Q-a))`.

Because the target is even and Q−a≥h+2, the right side has exact valuation h+1, forcing `v2(F(x)-1)=h`; dividing and multiplying by 3^h recovers y at target precision. Large x makes both odd cofactors u and v at least 5. All these are statements about **genuine** one-variable section transitions, not abstract arbitrary affine updates.

Independently, the same branch is affine over the integers:

```
2^c * E(x) = alpha*x + beta,
alpha = 3^h*(1+2^(a+1))  (odd),
beta  = 2^a * [2^(h+1)+3^h*(2a-3)].
```

Since q is odd, `2^c` is invertible modulo q. Therefore **on a fixed branch**, the next odd-q residue is determined solely by the previous odd-q residue, regardless of which huge positive representative realizes the branch. Any two integers congruent modulo q and sharing (a,h) produce congruent successors modulo q. This is the essential mixed-modulus transport fact.

## Reverse the whole path at binary precision, then impose the odd coordinate

For the given walk choose each exact pair (a_i,h_i) from a **real legal generic witness** of its corresponding edge. Such a witness satisfies `x_i mod2^p = r_i mod2^p` and `E(x_i) mod2^p=r_(i+1) mod2^p`. Even if its valuation a_i≥p or its odd run h_i is larger than p, its exact inverse formula remains valid at every sufficiently high precision.

Set `z_n=r_n mod2^p` and `Q_n=p`. Work backwards for i=n−1,...,0:

```
Q_i = Q_(i+1) + c_i = p + sum_{j=i}^{n-1} c_j,
z_i = T[Q_i,a_i,h_i](z_(i+1))  (mod2^Q_i).
```

Each target precision Q_(i+1) is at least p>=1, so the inverse-letter lemma applies throughout. **Projection to mod2^p** gives `z_i≡r_i`, by backward induction: the genuine edge witness with the chosen same (a_i,h_i) proves the same original inverse relation modulo2^p, and the exact inverse formula is compatible with reducing the target and parent mod powers of two. This remains true when `a_i>=p`, because then both source residues are automatically zero. No constraint on the odd-q residue has been imposed by this binary recursion.

Now apply CRT, because `gcd(2^P,q)=1`, to choose

```
x_star ≡ z_0  (mod2^P),
x_star ≡ r_0  (modq).
```

Take x in that arithmetic progression sufficiently large. Binary inverse induction forces *every* branch letter in sequence exactly, and produces the desired binary residue at each step. Simultaneously, use the affine odd-q congruence: the first source has odd coordinate r_0; for each next edge, its original witness with the same branch letter maps r_i modq to r_(i+1) modq. Induction therefore forces our genuine orbit to match **each** prescribed odd coordinate as well. Combining both residues by CRT gives the full modulo-m walk.

On the fixed entire branch sequence, composition has slope `A/2^C`. Shifting x by `2^P q =2^(p+C)q` changes the final integer exactly by `A*2^p q`; all letters and odd-q residues remain unchanged. There are infinitely many arbitrarily large legal witnesses in this progression. The density formulas follow from its exact period. QED.

## Reproducible audit, significance and remaining gap

The independent standard-library [verify_mixed_paths.py](verify_mixed_paths.py) constructs genuine generic sampled edges from literal positive integers and additional inverse-engineered large-h branches. It samples paths of lengths 1..12, including zero-residue revisits, then **reverses each complete path at enlarged dyadic precision**, imposes its initial odd-q residue by CRT, and checks all consecutive *actual integer* E returns, exact valuations, targets and affine slope. With deterministic seed 602026, the test passed **143,984** finite walks across **60 moduli** with p=1..6 and q in {1,3,5,7,9,11,15,21,25,35}. Included noninvertible odd factors 3 and 5 and composite q. This is finite corroboration; the proof above handles all p,q,n.

The theorem is a significant limitation on **finite symbolic quotient reasoning**: independent generic edge witnesses do not create a spurious finite quotient path, because *every such finite path* can be physically concatenated from some freely chosen start. It supplies no infinite path from any fixed start. A single fixed integer 10 can miss an arbitrarily large set of realized finite paths; nor does the theorem prove that every infinite quotient path has an ordinary positive-integer realizing start. It neither proves a halting witness nor an all-time invariant of the true Sheep blank orbit. The full all-p proof remains paper mathematics depending on the established source-connected one-variable section equation, not a Lean-certified import of the new all-modulus path-lifting theorem. External novelty and independent mathematical review are outstanding. Keep under `im-results/` pending those checks.
