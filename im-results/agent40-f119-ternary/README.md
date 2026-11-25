# F119: two-tag ternary acceleration and terminal exponent restriction

Machine: `1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB` (upstream #417 / suspect_15). This is a live member of the historical 608 holdout roster.

## Established theorem

For the copied upstream three-counter recurrence, blank-root halting is equivalent to reaching a section `(3^k,1)` with `k mod 12 = 0 or 3`. The immediately preceding section, whenever such a power is reached from a nonterminal root path, must have tag 1 and ternary valuation 1; its first coordinate is (9·3^k−33)/10 when k mod 4 = 3 and (9·3^k−39)/10 when k mod 4 = 0.

The first gate eliminates all other terminal exponent classes; the second gate below restricts them further to 0, 3, 39, 48 modulo 60 and is original-source accepted. None of these four classes has yet been proved unreachable. The new [modular obstruction](ModularObstruction.md) proves that every fixed-modulus generic tag-1 graph is strongly connected, excluding ultimately periodic section safety invariants (paper proof with a locally kernel-checked arithmetic core). The actual root decision remains open.

## Reduction

A section (x,c) denotes D(0,x−1,c), x≥4, c∈{1,2}; the initial section is (4,1). Factor x=3^h m with 3∤m. The following returns are exact:

* m=3t+1, t≥1: (x+c+h+t+2,1).
* m=3t+2: (x+c+h+t+3,1).
* m=1: let r=(c+x−1+h) mod 3. If r=0 the recurrence halts; otherwise the return is (x+c+h+4−2r,r).

Every nonterminal return increases x strictly. In the root-compatible section invariant, tag 2 occurs only at x=3^a+a+1, a≥2. Such a section and its generic successor lie strictly between consecutive powers. Power-to-power returns are also impossible.

For a generic tag-1 predecessor of 3^k, put p=3^h and M=3p+1. Powers of three modulo M are among ±3^j, 0≤j≤h. For h≥2 the necessary residue is p+h+3 or 2p+h+4, both excluded by the gaps between these signed powers. For h=0 the output is even. For h=1 the residue calculation modulo 10 gives the two formulas above. The halt test imposes k mod 3=0.

## Evidence and reproduction

`F119.lean` is a pure Std proof, checked locally with Lean 4.36.0-rc2. Run `lean F119.lean`. Main declarations: `F119.root_halts_iff`, `F119.incoming_power`, `F119.root_halts_iff_restricted_power`. The printed axiom sets are subsets of propext, Classical.choice and Quot.sound; no sorry or native_decide.

The proof currently uses a literal transcription of the arithmetic transition from Google DeepMind cryptids, Apache-2.0, commit 3647718b5df22e1a61462dec0376bd204526285a, [original module](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/M_1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_HHH1LB.lean). That module supplies the raw-machine acceleration theorem. The import-connected equivalence including the stronger second gate subsequently passed pinned original-source CI 45547394921; see source status below.

## Next obligation

Decide reachability from (4,1) of the two remaining power classes. A useful inverse formulation for tag-1 generic sources is y=(3p+1)t+pr+h+3+δ, where r∈{1,2}, p=3^h, δ=1 exactly for r=2. The inverse is finite for a given target, but a uniform proof over unbounded exponents needs stronger arithmetic structure.


## Second inverse gate (25 November 2026)

The restricted terminal powers have at most four remaining exponent classes modulo 60:
`k ≡ 0, 3, 39, 48 (mod 60)`. This eliminates six of the ten classes allowed by the first inverse gate. It does not assert that any remaining power is reachable.

For k ≥ 4, every first-parent target has the form 10y+C=3^(k+2), with C=39 when k≡0 (mod 12), C=33 when k≡3 (mod 12). Its predecessor cannot be a tag-2 exception or a pure-power return. Indeed 2·3^(k−1)<y<3^k; either exceptional source arises from 3^a with a≤k−1 and gives y≤(4·3^a+7a+18)/3 <2·3^(k−1). The root (4,1) is also outside this window.

For a generic tag-1 predecessor x=3^h(3t+r), r∈{1,2}, the target equation is

    3^(k+2) = 10[(3·3^h+1)t + 3^h r + h+3 + [r=2]] + C.

All h≥6 are impossible: set p=3^h, M=3p+1. Powers of 3 modulo M lie in the signed list ±3^j for 0≤j≤h. Since 2(39+10(h+4))<p, the required residue for r=1 is strictly between p and 2p+1, and for r=2 strictly between 2p+1 and 3p+1−p/3. Neither interval contains a signed power. For h<6 a full 120-exponent period modulo 10M suffices. A kernel-decided enumeration leaves exactly h=1, and the following necessary possibilities:

| k mod 60 | C | r | Second predecessor x |
| ---: | ---: | ---: | --- |
| 0 | 39 | 1 | (3^(k+4)−681)/100 |
| 3 | 33 | 2 | (3^(k+4)−687)/100 |
| 39 | 33 | 1 | (3^(k+4)−627)/100 |
| 48 | 39 | 2 | (3^(k+4)−741)/100 |

For k<4 the residue restriction follows directly from the earlier mod-12 restriction. Thus the exact local root-halting equivalence can restrict k to these four classes.

**Proof status:** [F119Inverse2.lean](F119Inverse2.lean) compiled with Lean 4.36.0-rc2, using only propext, Classical.choice and Quot.sound. [F119RootInverse2.lean](F119RootInverse2.lean) compiled locally against temporary exact-signature interfaces of the prior local recurrence; original dependency compilation is required before claiming full kernel closure. [F119SourceBridge.lean](F119SourceBridge.lean) transports every branch to the pinned original Cryptids acceleration and composes the four-class root equivalence. Its branch map and local stopping/iteration conversion were locally checked on literal definition mirrors; the original source import subsequently passed the manual audit described below. No mock interfaces are committed.

The next mathematical target is actual exclusion or attainment of the remaining four power families, preferably a root invariant or an unbounded inverse-tree argument rather than repeated finite-depth enumeration. The exact BB(6) champion bound remains unchanged.


## Uniform affine inverse theorem

This generalizes the two special inverse gates to arbitrary affine exponential targets. Write a target as (y,1) with D*y+C=3^N, D>0, 3∤D, C≥0. Let H,A≥2 satisfy

    2(C+D(H+4)) < 3^H,
    B(D,C,A) = (A+1)(D(6A+17)+3C) < 3^A.

Both inequalities persist at every larger index (proved by induction). Such H,A always exist because an exponential dominates a polynomial. If additionally

    3^N > D(2·3^A+3A+7)+C,

then **every root-invariant predecessor is generic tag 1 with h<H**, and conversely every legal such generic branch is an actual edge. See `F119AffineRoot.edge_iff_branch`. Thus symbolic expansion of each exponential-affine family is finite: for h=0,...,H−1 and r=1,2 check divisibility and positivity in the equation

    3^N = D(3·3^h+1)t + C + D(3^h r + H_r),
    H_r = h+3+[r=2].

The congruence is periodic in N modulo the multiplicative order of 3 modulo D(3·3^h+1), since this modulus is coprime to 3. Once a legal t is obtained, the exact predecessor has

    D' = D(3·3^h+1)
    C' = 3^h(3C+D(3H_r−r))
    N' = N+h+1
    D'x+C' = 3^N'.

The generic exclusion reduces D*r modulo 3 to 3q+u (u=1,2). Its target residue mod M=3·3^h+1 is u·3^h+E−q, E=C+D H_r, with 1<E−q<3^h/2. It lies strictly between consecutive signed-power residues. The pure-power exception yields 3^N=3^a D + (D(a+3)+C), impossible for 0<remainder<3^a. For the tag-2 exception x=3^a+a+1, exact factorization implies 3^h divides a+1, hence 3^h≤a+1. Multiplying the target by 3^(h+1) yields 3^(N+h+1)=3^a D(3·3^h+1)+E', where 0<E'≤B(D,C,a). For a≥A it is impossible by the same remainder argument. All a<A produce y≤2·3^A+3A+7, hence cannot meet the stated large-N bound. For N below the cutoff, check the finitely many exact low-exponent targets directly.

**Status:** All arithmetic lemmas in [F119AffineInverse.lean](F119AffineInverse.lean) compile locally with Lean 4.36.0-rc2 and ordinary kernel axioms only. [F119AffineRoot.lean](F119AffineRoot.lean) compiles against the temporary exact-signature F119 interface and actual affine arithmetic module; its only nonstandard axiom is the interface theorem invariant_power_tag, whose actual implementation is in F119.lean. Do not interpret the interface test as a complete source audit. This establishes a reusable finite branching theorem, not a proof that the infinite ancestry tree misses the blank root.

## 2026-11-25 source-audit checkpoint

Pinned original-source CI [45547394921](https://github.com/FlareZ123/bb6/actions/runs/45547394921) succeeded at 04:35:56Z. Its exact inputs were original F119 upstream module at 3647718b5df22e1a61462dec0376bd204526285a, F119.lean, F119Inverse2.lean, F119RootInverse2.lean, and F119SourceBridge.lean. The theorem `F119SourceBridge.raw_halts_iff_second_classes` depends only on propext, Classical.choice, Quot.sound. No whole-root decision follows merely from the four exponent classes. The generalized affine theorem is queued for the same exact source closure.
