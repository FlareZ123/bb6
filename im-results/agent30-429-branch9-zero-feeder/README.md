# BB429 branch-9 diagonal feeder and exceptional-parent sieve

**Mathematical scope.** This is an exact algebraic reduction of one branch-9 last-reset family in the genuine `BB429.next` accelerator, together with a *new necessary congruence restriction* on its exceptional inverse parents and a reproducible finite-depth inverse sieve. The algebra and modulo-32 exclusion are paper arguments using existing all-time blank-root invariants; the deeper census is exact-integer JavaScript computation, **not a compiled Lean proof**. This dossier does not establish that any pre-reset state is reachable or unreachable for every parameter. Machine #429 and BB(6) remain open.

## Authentic source, last-reset family, and full inverse grammar

The original six-state target is `1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA`. We use the exact return map `BB429.next` in [BB429Rank.lean](../agent5-429-rank/BB429Rank.lean). The original branch-9 last-reset equations for pre-reset `(x,y)`, burst length `n`, and reset parameter `d` are

    4*x = 2^(n+2)*(d+10) + 2*d - 3*n - 25,
    y   = 2*(x-d) + 1.

On `h=(2*d-3*n-13)/4=0` set `d=(3*n+13)/2`. The interesting integer subfamily, for `J≥2`, is

    n=8*2^J-11;    d=12*2^J-10;    N=n+J;
    (x,y)=(12*2^N-3, 24*2^N-24*2^J+15).

The first-branch predecessor for an odd first coordinate is `F⁻¹(a,b)=((a-3)/2,a+b)`. Its complete spine, for `0≤i≤N`, has the exact integer coordinates

    A_i = 12*2^(N-i)-3,
    B_i = 48*2^N-24*2^(N-i)-24*2^J+15-3*i.

At `i=N` this gives `(9,B_N)`. From the genuine source case split, nine has unique predecessor `(3,B_N+9)`, and three in this situation has unique predecessor `(0,z_J)`, where

    z_J=B_N+12=12*2^(N+2)-48*2^J+36-3*J.

These two inverse steps identify an **all-F feeder**, not the entire ancestry of `(x,y)`: exceptional predecessors must also be examined. All-F ancestry is ruled out immediately for odd `J` because then `z_J` is odd, whereas every transition to first coordinate zero has even second coordinate. This is not an exclusion of the pre-reset state itself.

The complete large-first-coordinate inverse grammar is

    F⁻¹(a,b)=((a-3)/2, a+b)              [odd a];
    S⁻¹(a,b)=((4*a+b-26)/4, (b+4)/2)    [odd a≥13, b≡2 mod4];
    E⁻¹(a,b)=((4*a+b-14)/4, b/2)        [even a≥6, b≡2 mod4].

Both `F` and `S` must be explored when admissible at an odd target. See [BB429NewResidue.lean](../agent6-harmonic429/BB429NewResidue.lean) for the source inverse lemmas.

## New exact S-parent parameterization and modulo-32 root obstruction

For any interior spine index `i`, `B_i≡3+i (mod4)`. Thus an S inverse exists only when

    i=4*k+3,   t=N-i≥1.

Its exact parent is

    X = 12*2^N+6*2^t-6*2^J-8-3*k,
    Y = 24*2^N-12*2^t-12*2^J+5-6*k.

When `J≥6` and `t≥6` the parent has

    (X mod32,Y mod32)=((-8-3*k) mod32,(5-6*k) mod32).

**Necessary condition:** If this genuine S-parent belongs to the blank-root orbit, then

    k mod32 ∈ {1,3,9,11,19,25,27}.

**Derivation, including all 25 excluded residues:** An even `k` gives even `X` and odd `Y`, contradicting the all-time positive-even source invariant `Y≡2 (mod8)`; this excludes 16 of 32 classes. For odd `k≡5,13,21,29 (mod32)` we get `X≡1 (mod8), Y≡3 (mod4)`, excluded by `BB429Mod8.Allowed`. For odd `k≡7,15,23,31 (mod32)` we have `X≡3 (mod4), (X+Y)≡6 (mod8)`, contradicted by the exact odd/odd predecessor theorem, which requires `X+Y≡2 (mod8)` for a sufficiently large authentic root state. Finally `k≡17 (mod32)` gives `X≡5 (mod32), Y≡7 (mod8)`, contradicting the strengthened five-mod-32 root row `Y mod8∈{2,4,5}`. These disjoint classes give `16+4+4+1=25` exclusions. The surviving seven classes are *not* certified reachable.

The root facts being consumed, rather than conjectured, are [BB429Mod8](../agent6-harmonic429/BB429Mod8.lean), [positive-even-eight](../agent39-429-1021/BB429RootEven8.lean), [odd/odd row source](../agent33-429-reset-boundary-rows/BB429ResetBoundaryRows.lean) and [the strengthened five row](../agent18-429-root-invariants/BB429SevenStrong.lean). Source-acceptance statuses of composed dependencies should be audited before turning this paper implication into a source-certified theorem.

This gives a uniform necessary condition on **every sufficiently interior exceptional branch**, not merely seven sampled values of `J`.

## Dyadic reverse-tree sieve: computation and proof obligation

[side_branch_sieve.js](side_branch_sieve.js) explores the complete `F/S/E` predecessor tree of the possible exceptional parent, rejecting a node whenever it violates a published all-time root necessary predicate. It uses JavaScript exact `BigInt` arithmetic and the following root filters:

* `BB429Mod8.Allowed`, positive-even mod-16 rows, strengthened seven/one/five root rows;
* odd/odd source rows of `BB429ResetBoundaryRows.odd_odd_rows`;
* ten forbidden small-modulus root cells from `BB429RootMod64R0` and `BB429RootMod64R2`.

The calculation depends only on `k` modulo `2^(D+6)` for a reverse depth `D`, provided `J,t≥D+6`. To see the precision bound, set `K=D+6` and compare the true initial parent with the signed dyadic representative

    (X₀,Y₀)=(-8-3*k, 5-6*k).

Their first difference is divisible by `2^K` and their second difference by `2^(K+1)`. Each inverse operation preserves an appropriately weighted congruence, losing at most one first-coordinate bit per level:

    F: (δX,δY) ↦ (δX/2, δX+δY)
    S or E: (δX,δY) ↦ (δX+δY/4, δY/2).

Consequently the reverse-tree branch guards and all predicates through mod64 in the first coordinate and mod32 in the second are invariant over each complete `k mod2^(D+6)` cylinder, for all depths ≤D. The actual first counters remain much larger than 33 under these conditions, so the source inverse grammar covers the tree and no small-counter exception is substituted. The representative is kept as a **signed integer throughout**; silently wrapping it modulo `2^K` during inverse expansion would invalidate the weighted precision.

The exact script census is:

| Inverse depth D | k modulus | Surviving residue classes | Fraction |
| ---: | ---: | ---: | ---: |
| 0 | 64 | 14 | 21.875% |
| 4 | 1024 | 56 | 5.46875% |
| 8 | 16384 | 188 | 1.14746% |
| 12 | 262144 | 788 | 0.30060% |
| 16 | 4194304 | 3068 | 0.0731468% |
| 18 | 16777216 | 4962 | 0.0295758% |

Thus the **depth-16 finite inverse search** rejects `4191236/4194304` classes of the `k` congruence parameter at sufficiently interior S parents, on the stated trusted-root-filter assumptions. The remaining 3,068 classes and all positions with `t<22` are open. This count is a reproducible algorithm output, **not a Lean kernel-certified cardinality theorem**, and the transitive source-axiom audit of the combined predicates has not been run for this new sieve. No density statement about machines or BB(6) follows.

The algorithm can be run with `node im-results/agent30-429-branch9-zero-feeder/side_branch_sieve.js 16`. The JavaScript source is deliberately standalone and the computed count includes a regression assertion; local runtime execution was unavailable in this invocation, so the script was not re-run after being committed. The numbers were produced by a functionally equivalent exact-BigInt interpreter in the available code execution runtime, not by Lean or original-machine simulation.

## Zero-parent bottleneck on the residual all-F spine

On the all-F route, `z_J` is even exactly when `J` is even. For `J=4m+2≥6`,

    z_J mod128 = (36-3J) mod128,
    u_top mod32 = (z_J-18)/4 mod32 = 3-3m mod32,
    u_odd mod32 = (z_J-2)/4 mod32 = 7-3m mod32.

The [genuine zero-two gateway](../agent18-429-root-invariants/BB429OddResetGate.lean) requires one of the following admissible predecessors:
the upper-boundary `(u,2u+2)` with `u mod16∈{0,4,5,8,9,12,13}`, or the odd-reset `(u,2u-3)` with `u mod32∈{7,13,15,21,29,31}`. Checking these two residue lists excludes **both possible predecessor kinds** for exactly

    m mod32 ∈ {3,4,7,11,12,15,16,19,20,22,23,27,28,31}.

This is a **new infinite exclusion of the zero-state ancestry for the all-F route**, not a full diagonal-state nonreachability proof. When `J=6` the upper-boundary candidate survives with `u≡0 (mod32)`, so Agent32's high-two/Junc classification is relevant. For `J=4m`, `z_J≡0 (mod4)` and the zero-two gateway does not apply; the broader even-zero predecessor grammar remains open.

The earlier exact DFS for individual `J=2,…,8` explored both exceptional alternatives and returned no surviving side leaf under a particular invariant collection; for odd `J=3,5,7` it found no candidate leaf at all, while for even `J=2,4,6,8` the only survivor was the all-F low-nine leaf. Those are finite experiments and do **not** establish a uniform claim in `J`.

## Unresolved mathematical quantifiers and next tests

1. Translate the depth-`D` residue pruning into a small source-attached Lean certificate generator on the exact original `BB429.next` inverse lemmas, with weighted modulus soundness and correct base guards. Source-check decisive all-natural congruence lemmas before claiming formal certification.
2. Prove a structural invariant for exceptional parents in the sparse surviving dyadic classes, rather than simply increasing `D` or listing more residues.
3. Close remaining `t<22` edge branches and the low-nine zero feeder. The present source-filter reductions, even if all accepted, leave these routes open.
4. Handle non-diagonal branch-9 `h≠0`; its previously derived first-even valuation filter is branch-local because alternative S predecessors remain.

No entry is promoted to `results/` while these gaps and external novelty review remain unresolved.
