# Finite-path lifting for the generic dyadic Sheep return map

**Agent 40, 7 November 2026. Intermediate mathematical theorem.** Every **finite directed walk** in the generic synthetic Sheep first-even quotient modulo `2^p` is realized by the *consecutive genuine returns of one sufficiently large positive integer*. The starting integers realizing a specified walk contain an explicit infinite arithmetic progression, with a quantitative density lower bound. This removes the changing-edge-witness ambiguity for **all finite paths**, extending the earlier single-target coherent completeness theorem and the [complete directed metric](README.md). It does **not** provide a single ordinary positive start realizing an infinite quotient path, and does not constrain the authentic Sheep blank-entry value **10**. No Sheep or BB(6) decision follows.

## Precise setting and theorem

Fix p>=1 and put m=2^p. The graph `G_p` consists of the even residues modulo m with an edge `r->s` precisely when some positive **generic** even-section Sheep first return `E(x)` witnesses source r and target s (mod m). The authentic generic formula is `F(2^a*u)=2^a*u+a+(u-1)/2`, with a>=1 and odd u>=5; write `F(x)-1=2^h*v`, v>=5 odd, then `E(x)=1+3^h*v`. This is the original published one-variable section, source-connected to the six-state Sheep machine by [Agent16](../agent16-sheep-even-return/README.md) and [CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547).

**Finite-path shadowing theorem.** For every natural n, every directed walk `r_0->r_1->...->r_n` of length n in `G_p`, and every bound N, there exists a positive even integer x>=N with `x==r_0 (mod m)` such that **all n genuine consecutive generic first-even returns are defined**, each input and intermediate odd cofactor is >=5, and `E^i(x)==r_i (mod m)` for 0<=i<=n. Moreover, the set of all qualifying x contains every sufficiently large positive integer in **one explicit residue class** modulo `2^P`, with

```
P = p + C,    C = sum_{i=0}^{n-1} (a_i+h_i+1) <= n*(p+1).
```

Consequently, qualifying starts have lower asymptotic density at least `2^(-P)` among positive integers and conditional lower density at least `2^(-C) >= 2^(-n*(p+1))` within the source congruence class `x==r_0 mod2^p`. All density statements concern freely selected positive integer starts.

## Exact inverse-letter input

For any precision q>=a+h+1, let `c=a+h+1`, and define

```
T[q,a,h](y) =
  2^a * (1+2^(a+1))^(-1) *
        (3-2*a + 2^(h+1)*3^(-h)*(y-1))  (mod 2^q).
```

The inverses are of odd numbers modulo `2^(q-a)`. This inverse residue has exact 2-adic valuation a, is compatible with projection to all lower powers of two, and depends only on `y mod2^(q-c)`. The [inverse-word proof](../agent22-sheep-mixed-hub/DYADIC-COMPLETENESS.md) shows the exact relation with genuine generic first-even returns. For completeness, the forward property needed here follows directly from algebra:

Given an even y modulo `2^(q-c)`, and any sufficiently large positive x congruent to `T[q,a,h](y)` modulo `2^q`, write x=2^a u (u odd). Setting D=1+2^(a+1), the inverse congruence yields

`D*u+2a-3 == 2^(h+1)*3^(-h)*(y-1) (mod 2^(q-a))`.

Because y is even and `q-a>=h+2`, the right side has exact valuation h+1. The generic first-section identity

`2*(F(x)-1)=D*u+2a-3`

therefore forces the **exact** odd-block valuation h, and the next even return is congruent to y modulo `2^(q-c)`. For sufficiently large x, all generic odd-part guards `u,v>=5` hold. The map on this branch has positive affine slope `3^h*D /2^c`, so sufficiently large lifts produce positive and growing returns.

## Choose the letters for an arbitrary quotient walk

For each prescribed edge `r_i->r_(i+1)`, fix a letter `(a_i,h_i)` as follows.

If `r_i !=0 (mod2^p)`, its valuation `a_i=v2(r_i)` is in [1,p−1]. An actual edge witness has some genuine h0. The standard inverse identity with **saturated** `h_i=min(h0,p-a_i-1)` gives

`r_i=T[p,a_i,h_i](r_(i+1))`, and `c_i=a_i+h_i+1<=p`.

If `r_i=0`, use the canonical convenient generic letter `(a_i,h_i)=(p,0)`, hence `c_i=p+1`. For any even y and any sufficiently high inverse precision q≥p+1, the residue `T[q,p,0](y)` has exact valuation p and therefore projects to zero modulo `2^p`. No restriction on the desired target is imposed. This also **constructs every zero-hub edge** without needing a separate quotient witness.

Thus, in both cases we have a fixed positive-cost inverse letter with `c_i<=p+1` and an exact forward relation that projects each target residue `r_(i+1)` to its prescribed source `r_i`.

## Reverse the entire walk once, then run it forwards

Set `C=sum_i c_i`, `P=p+C`. Start with the final even residue `z_n=r_n` at precision `q_n=p`. For i=n−1 down to 0, set

```
q_i = p + sum_{j=i}^{n-1} c_j = q_(i+1)+c_i,
z_i = T[q_i,a_i,h_i](z_(i+1)) mod 2^q_i.
```

Projection to `2^p` gives `z_i==r_i` at every i, by the letter choices and inverse-map compatibility. Let `x=z_0+2^P t`, with t an arbitrarily large nonnegative integer. It is even, positive, and has the source residue `r_0`. The exact inverse-letter forward property inductively forces branch `(a_i,h_i)`, and carries the physical successor to `z_(i+1)` at precision q_(i+1). Each target precision is at least p>=1, so no valuation ambiguity arises. Choose t sufficiently large once to meet all the finitely many generic cofactor guards. All n genuine returns occur in **one physical integer trajectory** and have the specified residues. QED.

There is an explicit stepwise affine sensitivity. Let `A=product_i [3^(h_i)*(1+2^(a_i+1))]`, which is odd. Changing t to t+1 raises the final `E^n(x)` by **exactly `A*2^p`**, and retains the entire prescribed finite branch sequence. Hence the full sufficiently large arithmetic progression is valid. The density claims follow since one residue modulo `2^P` appears once per period, and the compatible source residue modulo `2^p` once per `2^p`.

## Consequences, evidence, and limits

1. **Every finite path is physically concatenable**, with freely selected start. In particular, the exact-k cylinder distance formula in [README.md](README.md) also describes all real **coherent free-start** generic trajectories, as a corollary of the stronger result.
2. Given any finite history of quotient residues, there are infinitely many arbitrarily large genuine positive starts producing exactly that history, even when the history revisits residue zero. Thus a putative obstruction to a finite quotient walk cannot be justified merely by saying that its individual edge witnesses differ. The infinite deterministic orbit from a fixed prescribed start is a separate problem.
3. Because the graph is strongly connected by Agent22's theorem and has a zero self-loop, every finite path can be followed by an arbitrary desired finite target path after a connecting graph walk. Finite symbolic mixing is genuine for selectable starts, with no claim of a universal time bound from x=10.

[verify_paths.py](verify_paths.py) independently enumerates `G_p`, selects inverse letters for every prescribed edge, reverses each complete random walk at rising precision, then checks **every literal generic integer first-even return**, exact (a,h), intermediate residues, cofactor bounds and optional final affine slope. With seed 622026 it passed **16,200** independently sampled walks of lengths 1..12 across precisions p=1..9, including paths through zero. This is a finite check. The theorem is a rigorous paper derivation relying on the prior all-p inverse equation and canonical edge completeness, **not** a new source-importing Lean4 all-parameter theorem. The original blank-root Sheep machine and the global value BB(6) remain unresolved.
