# Uniform predecessor-valuation cutoff for symbolic Sheep families with arbitrary coefficients

**Status:** new intermediate mathematical tool, with complete written proof and **Lean-kernel-checked all-exponent modular gap** in [GeneralOddGap.lean](./GeneralOddGap.lean), plus exact-integer tests. The abstract tail-persistence lemma is also Lean checked. The full machine-to-symbolic-inverse framework has not yet been composed in Lean. Existing Agent 14 results already give the stronger special-case c=3 immediate-parent table, and Agent 17's earlier symbolic sieve handles c=1. This note generalizes the *symbolic family language* to all c>0, including nonzero offsets b and arbitrary odd denominators d. It does not classify a blank orbit, determine the Sheep Machine's behavior, or improve a BB(6) bound.

## Setup and theorem

Let `c>=1`, `s>=0`, `b` an integer, and `d>=1` odd. Represent a target family by

    Y(j) = (c*2^(j+s) + b)/d.

For a genuine *generic* Sheep return edge `x=2^a*u -> Y(j)` with `u>=5` odd, multiplication of the published exact return formula yields

    c*2^(j+s+1) = d*(2^(a+1)+1)*u + K(a),
    K(a) = d*(2a-1)-2b.                        (1)

Here `K(a)` is always odd, even when b is negative. Write `M(a)=2^(a+1)+1`. In particular, a necessary condition for a predecessor at valuation a is

    c*2^(j+s+1) ≡ K(a) (mod M(a)).            (2)

**Kernel-checked general odd-remainder gap theorem** (`BB6Sheep17Gap.no_power_signed_gap`). For every c>=1, a>=0, odd integer K, and `M=2^(a+1)+1`, if

    c < K,    M > c*(c+K)+K,                 (3)

then `c*2^n ≢ K (mod M)` for **every natural n**. Thus any a satisfying (3), with `K=K(a)`, is impossible for every exponent j in (1). The argument only requires K odd; c need not be odd.

**Proof.** Euclidean division by `a+1` and `2^(a+1)≡−1 (mod M)` reduce the residues of `c*2^n` to `±c*2^r`, `0<=r<=a`. Put `R=2^r`. If r=0, the two positive representatives cannot equal K, since `c<K` and `c+K<M`. For r>=1 the integer `V=cR` is even and K is odd.

Suppose first `R<=c+K`. From (3), `0<V` and `V+K<=c*(c+K)+K<M`. Thus the residue of V is V itself, which is even and cannot equal K; it also cannot equal `-K (mod M)` because V+K<M.

Suppose instead `R>c+K`. Because `R<=2^a` and `M>2^(a+1)`, we have `0<V<c*M`. Write `q=floor(V/M)`, so `0<=q<c`. If `V≡K (mod M)`, then `V=qM+K` and, reducing modulo R using `M≡1 (mod R)`, one gets `R | (q+K)`, impossible because `0<q+K<c+K<R`. If `V≡−K (mod M)`, then `V=(q+1)M-K` and reduction gives `R | (K-q-1)`, impossible because `0<K-q-1<K<R` (as `K>c>=q+1`). Every case contradicts (2). QED.

**Effective finite cutoff.** The integer `K(a)=d*(2a-1)-2b` grows linearly with a and `M(a)` exponentially. Therefore an A can always be found satisfying

    K(A)>c,
    M(A)>c*(c+K(A))+K(A),
    M(A)>=2*d*(c+1)+1.                      (4)

These conditions persist for every a>=A. Indeed `K(a+1)=K(a)+2d` and `M(a+1)=2*M(a)-1`; the RHS of the middle bound grows exactly by `2d*(c+1)`, which is less than the growth of M by the reserve condition. This persistence step is proved in `GeneralTailPersistence.lean`, compiled locally in Lean 4.36.0-rc2 with only `[propext, Quot.sound]` and no `sorryAx`.

Consequently **every genuine generic parent of every target in the family has valuation `a<A`**. A is independent of exponent j. The general symbolic parent remains in the same coefficient-c language:

    parent_a(c,s,b,d) =
      (c, s+a+1, 2^(a+1)*b + 2^a*d*(1-2a), d*(2^(a+1)+1)).

This is immediate from Agent 17's already Lean-checked `FamilyCore.generic_parent_identity` after substituting `q=c*2^(j+s)`; the new gap theorem supplies the previously missing uniform high-a bound for c different from one. Exhausting the finite valuations a<A requires exact period checks modulo d*M(a), as in `PeriodCore.lean`; the present result is independent of any untrusted claimed multiplicative order.

## Concrete bounds and computational audit

For unshifted integer targets `Y(j)=c*2^j` with b=0,d=1, the conservative general cutoff gives:

| c | Generic parent valuation must satisfy |
|---:|---|
| 1 | a<2 |
| 3 | a<5 |
| 5 | a<6 |
| 7 | a<7 |
| 9 | a<7 |
| 15 | a<9 |
| 31 | a<17 |

Some are intentionally weaker than specialized exact classifications, notably Agent 14's c=3 bound a<=3. Unlike the special-case proofs, the same algorithm applies to arbitrary rational-exponential symbolic descendants including b!=0.

Run `python symbolic_odd_coefficient.py` (Python 3.10+, standard library only). In a local Python 3.11 run it passed **7,728** exact high-valuation cutoff/complete-modulus-period tests, across 23 coefficients, 7 signed offsets and 4 odd denominators, plus **20,000** exact algebra and genuine generic section-edge tests with seed 17062026. The tests are finite regression evidence; the all-exponent modular exclusion is now independently **proved in Lean 4.36.0-rc2** in `GeneralOddGap.lean` under the name `no_power_signed_gap`. Its full proof was compiled locally, and the final axiom audit listed only `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. `GeneralTailPersistence.lean` separately compiled locally with `[propext, Quot.sound]`.

## Scope and next constructive application

The bound eliminates the unbounded valuation parameter when building a finite backward tree for any fixed coefficient-c symbolic target. It **does not** eliminate every predecessor, including arbitrary-depth zero-valuation corridors. A future extension of `symbolic_sieve.py` can track `(c,s,b,d)` and exploit the uniform cutoff, while using the exceptional `u=3` branch separately and retaining source reachability checks. To make progress toward full Sheep closure, use the generalized families to discover a valid forward reachable-set invariant from 5 or an unbounded-depth argument. Do not interpret increased finite residue coverage as proof of a machine decision.

## Further uniformity

[EXCEPTIONAL-TAIL.md](./EXCEPTIONAL-TAIL.md) independently establishes an explicit all-exponent cutoff for exceptional `u=3` parents of **every** fixed positive-coefficient symbolic family. Combined with the generic `a<A` theorem here, both branching mechanisms are controlled above a computable exponent threshold. This produces a genuinely reusable finite-local-branch algorithm, while leaving arbitrary inverse depth and the blank-origin reachability problem unresolved.
