# BB429 branch-9 diagonal feeder and exceptional-parent sieve

**Latest advance:** complete locally kernel-checked blank-root exclusions for the J=9 and J=14 diagonal targets, with a reusable signed inverse certificate theorem. See the certificate section below. Full-module CI pending.

**Mathematical scope.** This dossier combines an exact algebraic branch-9 diagonal last-reset subfamily of the genuine `BB429.next` accelerator with source-kernel-checked all-time blank-root necessary conditions. They now exclude **27/32** exceptional-parent parameter classes modulo 32, **21/32** all-F zero-two predecessor parameter classes modulo 32, and all but **6/256** burst-index classes on the all-F central-zero branch. The previously CI-cited exported Lean theorems have been compiled against the unchanged original source closure and report only `[propext, Classical.choice, Quot.sound]`, not `sorryAx`. A separate deeper exact-integer dyadic inverse sieve remains computational, not yet a Lean proof. The algebraic inverse paths and conditional root exclusions do **not** determine reachability for every parameter, the behavior of machine #429, or BB(6).

## Complete diagonal certificate for J=9

The new theorem `BB429Branch9J9.no_diagonal_J9` excludes the entire target
`(12*2^4094-3,24*2^4094-24*2^9+15)` from the original accelerator's
blank-root Reach relation, at every return time. This is a fixed-exponent
root exclusion, not a decision of #429.

- [BB429DyadicTransport.lean](BB429DyadicTransport.lean) proves generic signed inverse-tree soundness. Near(m,a,b,x,y) requires differences divisible by m and 2m respectively. Each genuine F/S/E inverse transports Near(2m) to Near(m). A bound x+3 >= 36*2^d keeps the genuine predecessors in the high-output grammar throughout depth d.
- [BB429DyadicSource.lean](BB429DyadicSource.lean) instantiates the checker with the existing root mod-8 Allowed theorem and genuine inverse grammar.
- [BB429Branch9Diagonal.lean](BB429Branch9Diagonal.lean) retains the exact 2^t and 2^J terms and removes only the common top 2^N contribution, eliminating the old t >= d+6 limitation. Its all-spine theorem converts a complete exceptional-index certificate and even N into nonreachability. The final all-F leaf (9,b) with b odd has unique predecessors (3,b+9) and (0,b+12); the latter violates Allowed.
- [BB429Branch9J9.lean](BB429Branch9J9.lean) checks all 1023 indices by kernel reduction at depth 18 and instantiates the all-spine theorem.

Local Lean 4.36.0-rc2 compiled all four modules against the exact relevant declarations copied from the repository accelerator modules. The finite certificate has no axioms; the root exclusion has only propext, Classical.choice and Quot.sound. Full-module source CI is pending. The finite certificate uses decide, not native_decide. No raw-machine source compilation is asserted here.

The same basic-filter algorithm suggests complete exceptional-index rejection for J=11,13,15,17, but these are exploratory computations only. The unbounded J quantifier and even-J all-F feeders remain open.

## Complete even-exponent diagonal exclusion: J=14

The second complete root exclusion is `BB429Branch9J14.no_diagonal_J14`:
the target (12*2^131075-3,24*2^131075-24*2^14+15) is unreachable from
the genuine accelerator root, for every return time. Here N is odd, so
the previous odd-J all-F parity argument is unavailable.

[BB429Branch9Clip.lean](BB429Branch9Clip.lean) safely clips every power
whose exponent is at least d+6. Its generalized spine theorem accepts
a proof of side-parent exclusion and a separate proof excluding the
unique all-F zero feeder. The exact zero-two source grammar has precisely
the upper boundary and odd-reset alternatives. The generic signed
zero-two certificate rejects them both for J=14, using q=-196614
and depth 1.

[BB429Branch9Cover.lean](BB429Branch9Cover.lean) proves low-bit trie
certificate soundness, with whole-class rejection at internal nodes
and exact clipped leaf checks. The high-counter and interior exponent
guards are explicit, so the proof covers every genuine state in each
residue class, not merely its representative.

[BB429Branch9J14.lean](BB429Branch9J14.lean) checks the interior interval
0 <= k < 32752 using the certified trie and all 16 remaining k individually.
Both finite certificates use `decide +kernel` (no compiler-trust axiom).
Local Lean 4.36.0-rc2 accepted all three modules against exact relevant
source declarations: both certificates axiom-free, the final root
exclusion standard axioms only. Full unchanged-module CI pending.

The technique also separates the unbounded research obligations:
all exceptional indices for general J, and the zero feeder, including
the additional zero-mod-four ancestry for J divisible by four. No
blank-run decision or BB(6) bound follows yet.

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

When `J≥5` and `t≥5` the parent has

    (X mod32,Y mod32)=((-8-3*k) mod32,(5-6*k) mod32).

**Source-certified theorem:** If this genuine S-parent belongs to the blank-root orbit and `J,t≥5`, then

    k mod32 ∈ {1,3,9,11,19,25,27}.

**Derivation, including all 25 excluded residues:** An even `k` gives even `X` and odd `Y`, contradicting the all-time positive-even source invariant `Y≡2 (mod8)`; this excludes 16 of 32 classes. For odd `k≡5,13,21,29 (mod32)` we get `X≡1 (mod8), Y≡3 (mod4)`, excluded by `BB429Mod8.Allowed`. For odd `k≡7,15,23,31 (mod32)` we have `X≡3 (mod4), (X+Y)≡6 (mod8)`, contradicted by the exact odd/odd predecessor theorem, which requires `X+Y≡2 (mod8)` for a sufficiently large authentic root state. Finally `k≡17 (mod32)` gives `X≡5 (mod32), Y≡7 (mod8)`, contradicting the strengthened five-mod-32 root row `Y mod8∈{2,4,5}`. These disjoint classes give `16+4+4+1=25` exclusions. The surviving seven classes are *not* certified reachable.

The checked source [BB429Branch9SideRoot.lean](BB429Branch9SideRoot.lean) proves the abstract root theorem `side_parent_k_mod32` and the parametric power-of-two theorem `diagonal_side_parent_k_mod32`, importing unchanged [BB429NewResidue](../agent6-harmonic429/BB429NewResidue.lean), [BB429Mod8](../agent6-harmonic429/BB429Mod8.lean), [positive-even-eight](../agent39-429-1021/BB429RootEven8.lean), and [the strengthened five row](../agent18-429-root-invariants/BB429SevenStrong.lean). The odd/odd sum obstruction is proved **directly** from the exact `odd_back` inverse lemma and the positive-even-eight theorem, not assumed from an independently compiled wrapper. The exact source closure and exported axiom profiles passed [manual CI 45112940106](https://github.com/FlareZ123/bb6/actions/runs/45112940106) at Lean 4.36.0-rc2, source commit `b055e879cf6781317b4159811a8daae9ec37ff3a`. This is an all-natural implication about authentic blank-root reachability, not a synthetic-state experiment.

**Forced-one-inverse refinement (kernel-checked).** The exceptional parent has odd second coordinate, so the exact `odd_back` source lemma forces the F predecessor. If `k≡3 (mod16)`, its positive-even first counter is `2 (mod4)` but its second coordinate is `2 (mod16)`, contradicting [BB429Even16.rooted_even_sixteen](../agent30-429-even16/BB429Even16.lean), which requires `10 (mod16)`. The stronger source theorem [BB429Branch9SideStrong.lean](BB429Branch9SideStrong.lean) therefore restricts every sufficiently interior exceptional parent (`J,t≥5`, first counter `X≥129`) to

    k mod32 ∈ {1,9,11,25,27}.

This **excludes 27 of 32 k residues**, uniformly over the burst parameters. Its abstract and exact-power theorems passed [CI 45114836298](https://github.com/FlareZ123/bb6/actions/runs/45114836298), without `sorryAx`. A two-inverse-step source proof candidate [BB429Branch9SideDepth2.lean](BB429Branch9SideDepth2.lean) aims at eleven remaining classes modulo 128; treat that additional cut as unverified until its separate source job succeeds.


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

## Exceptional parents have an exact dyadic gap independent of the outer burst

The full S-parent formula above gives the **parameter-free identity**

    2*X + 21 = Y + 24*2^t,
    d := X - (Y-1)/2 = 12*2^t - 10.

Here `Y` is odd, and `d` is the source map's actual odd-gap counter, independent of the much larger `N` and `J` and of the spine index `k`. In fact, for `t≥1`, `d` is even and `d≥14`; the genuine odd-gap source branch, not an artificial inverse transition, maps

    (X,Y) -> (d+7,2*Y-4) = (12*2^t-3,B_(4k+3)).

Thus every potential exceptional ancestor joins the same first-coordinate tower as the ordinary F spine, but by **encoding the remaining distance t as its gap**. The source formula itself proves this algebraic statement, without assuming blank reachability. This is a stronger structural handle than the dyadic residue frequency alone: the next productive investigation should seek an all-time root invariant on the joint *first-coordinate/gap* pair, or a monotone obstruction across repeated F/S switching. Merely classifying `X` by bounded congruences discards the exact gap `12*2^t-10`.

For clarity, an inverse tree with a fixed total rank `R=2u+w` can be parameterized by the leading `2^N` coefficient of the first counter. The full F inverse sends its leading coefficient `a→a/2`, whereas S/E send `a→(a+24)/2` when the rank's leading coefficient is `48`. On the normalized coefficient `p=a/24`, this is the binary contraction `p→p/2` versus `p→(p+1)/2`. This is an *algebraic branch-encoding observation*, not a proof that every binary word is source-admissible. The real guards, lower-order terms, and finite natural first counters are the essential additional data.

## A 2-adic ghost spine obstructs uniform shallow congruence pruning

There is a simple structural explanation for why growing the published all-time root residue sieve cannot, **by itself**, eliminate the long all-F spine. The affine F predecessor formula on integers is

    F⁻¹(a,b)=((a-3)/2, a+b).

In the 2-adic limit the first coordinate `a=-3` is a fixed point:

    F⁻¹(-3,b)=(-3,b-3).

The residue `-3` is `5 mod8, 13 mod16, 29 mod32, 61 mod64`.

**Stronger arithmetic obstruction to unguarded modular methods.** Consider the affine map `F(u,w)=(2u+3,w-2u-3)` as a map on **integers without the source branch guard**. Its formal iterates from the origin can be evaluated in closed form:

    F^n(0,0) = (3*(2^n-1), 3*n-6*(2^n-1)).

For every fixed `K≥1` and `n≥K`, the first coordinate is `-3 (mod2^K)`, while the second is `3n+6 (mod2^K)`. Because `gcd(3,2^K)=1`, as `n≥K` varies every possible second-coordinate residue is attained on the row with first coordinate `-3 (mod2^K)`. Therefore **any modulo-`2^K` overapproximation that contains the origin and permits the unguarded affine F edge at every residue state must contain the entire ghost row**; it cannot use any such invariant to reject that row. The proof is the elementary induction for the displayed formula and invertibility of three; it is not a computational census. It does **not** say that the actual blank machine reaches any of those states: the formal integer orbit has negative second coordinates and does not satisfy the real F branch guard. This distinguishes a structural limitation of a particular abstract semantics from a claim about real reachability.
 **All the particular all-time predicates currently consumed by `side_branch_sieve.js` admit every second-coordinate residue at that first-coordinate 2-adic point:** the basic `Allowed` invariant imposes no restriction when the first coordinate is `5 mod8`; the strong seven/one/five rows, the even16 law, and the ten listed forbidden mod64 cells do not apply; the odd/odd row for first `13 mod16` imposes no second-coordinate restriction. Thus the formal *residue filter* accepts the entire infinite ghost chain `(-3,b-3i)` for all finite `i`. This is a check of the listed filter definitions, **not** a claim that a negative first counter is a genuine natural machine state.

The real spine has `A_i=12·2^(N-i)-3`. For any fixed modulus `2^K` and finite inverse depth `D` with `N-i≥K+D`, its successive first coordinates agree with the ghost value `-3` modulo `2^K`; and its successive second coordinates agree with a decrement of 3 per F step after the high-power terms vanish. Consequently **no finite-depth restriction based only on these specific bounded-residue predicates can eliminate the generic interior all-F branch**: at finite 2-adic precision it is indistinguishable from the admitted ghost spine. This limits this *particular* sieve, not all conceivable modular invariants, and says nothing about the genuine root reachability of the terminal `(9,3,0)` states. A productive route needs a global invariant that distinguishes natural finite first counters from their 2-adic shadows, a new source invariant constraining first `-3` residues, or a complete analysis at the small-counter end rather than just deeper uniform congruence tests.

## Stronger source-kernel-checked zero-return root gates

For all genuine blank-root visits with a parent first counter `u≥129`, the exact source map yields **two** possible predecessors of a zero output with second coordinate `z≡2 (mod4)`:

- **Upper**: input `(u,2u+2)`, output `(0,4u+18)`; [BB429UpperBoundary.rooted_upper_mod16](BB429UpperBoundary.lean) proves `u mod16∈{0,5,8,13}`, versus seven previously allowed classes. [CI 45114018547](https://github.com/FlareZ123/bb6/actions/runs/45114018547).
- **Odd reset**: input `(u,2u-3)`, output `(0,4u+2)`; [BB429OddResetImproved.rooted_odd_reset_necessary_three](BB429OddResetImproved.lean) proves `u mod32∈{13,15,29}`, eliminating `7,21,31` from the older six-class root gate. The proof uses the source F/E inverses and all-time even16, odd/odd, one-nine rows, not a synthetic tape assumption. [CI 45114373790](https://github.com/FlareZ123/bb6/actions/runs/45114373790).

In the diagonal all-F feeder with `J=4m+2≥6`, `z_J+12m≡30 (mod128)`. Substituting the two branches gives exactly the following **source-certified necessary residue set**:

    m mod32 ∈ {1,2,8,9,10,14,17,18,25,26,30}.

The 21 other residue classes cannot be blank-root ancestors of `(0,z_J)` through either zero-two source branch with `u≥129`. The theorem [BB429ZeroTwoThree.diagonal_zero_two_m_power_eleven](BB429ZeroTwoThree.lean) establishes this for all natural parameters satisfying the exact power equation, not just sampled exponents. [CI 45114573957](https://github.com/FlareZ123/bb6/actions/runs/45114573957), exact original source, standard axioms only. It does not preclude any S predecessor on the earlier diagonal spine.

For `J≡0 (mod4)`, the feeder `z_J` is `0 (mod4)`, and these zero-two gateway theorems do **not** apply. However, one candidate is the **central reset** input `(u,2u)`, output `(0,4u+12)`. [BB429CenterLine.rooted_center_mod32](BB429CenterLine.lean) initially restricted `u mod32` to `{13,17,25,29}`; its source refinement [BB429CenterLineMod64.rooted_center_mod64](BB429CenterLineMod64.lean) restricts `u mod64` to `{13,17,29,45,57,61}`, excluding two further dyadic cylinders with genuinely reachable inverse predecessors. Combining `4u+12=z_J` with the exact power formula yields

    J mod256 ∈ {12,76,140,156,188,204}

as a **necessary** condition for the central-reset branch of the all-F route (`J≥8`, `N≥6`, `u≥129`). The [Lean theorem `diagonal_zero_center_power_j_mod256`](BB429CenterLineMod64.lean) was accepted by [CI 45114582855](https://github.com/FlareZ123/bb6/actions/runs/45114582855). This excludes the central source branch for 250 of 256 exponent classes, but the `0 (mod4)` zero-output grammar contains **other branches** (including the odd-gap resets) that remain unclosed. It is not a full all-F exclusion for `J≡0 (mod4)`.

These restrictions concern authentic blank-root *necessity* on named inverse routes, and are not claims of positive reachability or nonhalting of machine #429.

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

1. The generic weighted inverse checker and complete J=9 and J=14 applications are locally kernel-checked. Full-module acceptance is the next source gate. The old stronger-filter numerical census remains a separate uncertified computation.
2. Prove a structural invariant for exceptional parents in the sparse surviving dyadic classes, rather than simply increasing `D` or listing more residues.
3. Generalize the exact-power certificates beyond fixed J and close the low-nine zero feeder, especially the `z≡0 (mod4)` non-central reset grammar. The present source-filter reductions, even if all accepted, leave these routes open.
4. Handle non-diagonal branch-9 `h≠0`; its previously derived first-even valuation filter is branch-local because alternative S predecessors remain.

The 27/32 source theorem and 21/32 zero-two gateway are genuine all-parameter restrictions on named conditional feeders, not nonhalting proofs for #429. No entry is promoted to `results/` while the unresolved alternative routes, a decision consequence, and external novelty review remain open.
