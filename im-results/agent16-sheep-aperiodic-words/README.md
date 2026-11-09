# Sheep: arithmetic obstruction to eventually periodic generic branch words

**Intermediate structural result, 9 November 2026.** For the source-derived Sheep first-even map, no infinite positive-integer trajectory consisting of generic source-compatible even-return edges can have an eventually periodic itinerary of complete generic branches `(a,h)`. The necessary strict growth is itself proved from those equations, so the central generic-path impossibility does not need growth as an external hypothesis. More quantitatively, if a nonempty word of total precision cost `C` repeats `r+1` times, its first boundary increment is divisible by `2^(r*C)`. This gives an effective logarithmic bound on how long any fixed branch block can repeat from a prescribed positive start. The entire arithmetic result is checked by the local Lean 4.36.0-rc2 kernel with ordinary logical axioms; the actual six-state source-to-even-map equivalence is an **independent already-certified dependency**, not reimported here. It does **not** prove Sheep nonhalting, a BB(6) bound, or a new root decision.

## Exact branch-word arithmetic

The genuine even-return section starts at 10. Its generic branch from `x=2^a*u` (`a>=1`, `u>=5` odd), with `F(x)-1=2^h*v` (`v` odd), has `E(x)=1+3^h*v` and obeys

```
(2^(a+1)+1)*u+2*a = 2^(h+1)*v+3.
```

Thus each generic branch has the exact **natural-number** affine identity

```
L*E(x)+Q=N*x+P,
L=2^(a+h+1), N=3^h*(2^(a+1)+1),
P=L+2^a*3^h*(2*a), Q=2^a*3^h*3.
```

For two consecutive branches with parameters `p=(L1,N1,P1,Q1)` and `q=(L2,N2,P2,Q2)`, their composite parameters are
`(L1*L2, N1*N2, N2*P1+L1*P2, L1*Q2+N2*Q1)`. Induction gives for every finite word `w` a single affine identity
`L_w*y+Q_w=N_w*x+P_w` with

```
L_w = 2^C,   C=sum over branches (a+h+1),
N_w = product over branches [3^h*(2^(a+1)+1)] (odd).
```

In particular `gcd(L_w,N_w)=1`. For any nonempty word, `C>0` and `L_w>=2`.

Suppose consecutive word-boundary states `x_0,x_1,...` repeat this same affine block. Subtract adjacent instances of its fixed affine equation. Since states strictly increase, their differences `d_i=x_(i+1)-x_i` are positive natural numbers satisfying
`L_w*d_(i+1)=N_w*d_i`. Coprimality implies, inductively, `L_w^r | d_0` after any `r` such adjacent links. In particular `2^(C*r)<=d_0`. Such links cannot exist for every natural `r`; taking `r=d_0` contradicts `d_0<L_w^d_0`.

The authentic generic even-section map strictly increases on its positive domain (see the source-equivalence theorem below). Its exceptional odd-cofactor-three sources are `x=3*2^a`. A putative eventually periodic branch itinerary uses only finitely many valuations `a`, and a strictly increasing orbit can therefore encounter only finitely many of these exceptional values. Its infinite tail would be generic and give the proved contradiction. This last corollary is a mathematical composition with the already-certified source semantics, **not a new source-imported Lean theorem**.

## Verification and reproduction

Five Lean modules, compiled in dependency order with `Std` under Lean 4.36.0-rc2:

1. [CoprimeAffine.lean](CoprimeAffine.lean) proves `finite_chain_gap_divisibility`, `finite_chain_gap_lower_bound`, `coprime_expansion_no_infinite_chain`, and `coprime_affine_no_infinite_growth`.
2. [SheepAffine.lean](SheepAffine.lean) proves `original_generic_algebra`, exact arbitrary-word affine composition `word_path_holds`, and `word_coprime`, `word_scale`, `nonempty_word_scale_gt_one`.
3. [SheepAperiodic.lean](SheepAperiodic.lean) proves `no_infinite_repeated_word` for every nonempty word and every strictly increasing infinite sequence of source-derived generic branch equations.
4. [SheepFinite.lean](SheepFinite.lean) proves the direct finite word-level quantitative result `word_repetition_gap_bound`: for every sequence of `n+1` identical complete generic words along a strictly increasing trajectory, `2^(n*C(w)) <= x_1-x_0`. This closes the finite-boundary inference inside Lean, without relying on a paper-only composition.
5. [SheepPhysicalGeneric.lean](SheepPhysicalGeneric.lean) introduces the explicit source-compatible generic even-edge relation with a>=1, odd source cofactor u>=5 and odd output cofactor v>=1, derives its strict growth directly from the Diophantine equation, transfers each edge to the affine word certificate, and proves `no_infinite_genuine_generic_word` with **no assumed monotonicity of the given trajectory**. The genuine edge algebra matches the source-connected even-map formula, but this new module itself does not import the original physical Turing machine.

All main declarations compile locally with printed axioms restricted to `[propext, Quot.sound]` (and subsets); no `sorry`, `admit`, or `native_decide`. UTF-8 SHA-256 hashes of the checked sources: CoprimeAffine `9678c0b7bda2ff9977422c17747630542bf51100048b9210e06d7bcbb6f4fea1`, SheepAffine `9304dddff6bc6b179a9f972e9820a6c801118ec2bdc3aa4396667f04a777df7e`, SheepAperiodic `9d0bd7cf8e489cbabe06875ef19aeb20f2b6cf3582be56f48d3f265f423f7cfd`, SheepFinite `3a07e541cf584665fe1bed5904591a984dbfb064f559022b9a7a1ca61ba86e2b`, SheepPhysicalGeneric `8f215ae60ff5e324cc2894ac9769842636bf1c1af467a9d198ed83f2a8df19f2`.

For standalone checking, place all three files in one Lean search directory, compile `SheepAffine.lean` and `CoprimeAffine.lean` to `.olean` files, then compile `SheepAperiodic.lean`, `SheepFinite.lean`, and `SheepPhysicalGeneric.lean`. The files require only Lean's `Std`. The branch algebra is tied to the published Sheep generic section formula via the explicit Diophantine identity, and a separate [original-machine source bridge](../agent16-sheep-even-return/README.md) was already verified in [CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547).

## Relationship to earlier work, limitations and next use

Agent22's [full-branch 2-adic Bernoulli coding](../agent22-sheep-2adic-bernoulli/README.md) already gives the word-cylinder parameters and the entire measure-theoretic generic picture. This arithmetic result makes a **pointwise** integer-orbit consequence explicit and formally proves the divisibility-growth obstruction. It should not be represented as independent academic novelty without checking prior art. In particular, the resulting nonperiodicity is compatible with the existing 14-bit finite-word universality of the authentic Sheep root prefix.

Every infinite genuinely positive Sheep orbit, if it exists, must have an aperiodic branch code. This is a structural restriction on possible successful forward invariants, but says nothing about whether the specific root 10 instead reaches some halting power of two at a finite time. The next decisive line is to exploit **nonperiodic, root-specific** constraints that forbid *all* halting powers, rather than generate additional finite quotient or branch-residue exclusions.
