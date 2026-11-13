# Exact parameter congruence for the second strict image family

## Statement

Let

**K(j,m) = 2^(2m+2)(j+3) - (j+3m+5).**

The second strict sixth/seventh image family is

**V(u,v) = (641+1024u, 574+1024v)**,

with sector condition

**(u+v) mod 16 = (15+4u) mod 16.**

Its exact pullback through the original high-stop equation is the single affine congruence cylinder

**j mod 512 = 319**, and **(3m+7j+14025) mod 16384 = 0**.

For all natural j,m, this is equivalent to the existence of u,v such that

- j = 319+512u;
- K(j,m) = 574+1024v;
- (u+v) mod 16 = (15+4u) mod 16.

In particular, the pullback forces m mod 512 = 42, hence m >= 42. No separate m >= 7 hypothesis is needed in the final parameter description.

## Proof

Write P = 2^(2m+2)(j+3). The elementary bound

**j+3m+5 <= 2^(2m+2)(j+3)**

holds for all j,m, so

**K+j+3m+5 = P.** (1)

### Image-family membership implies the congruences

Suppose j=319+512u, K=574+1024v, and v = 15+3u (mod 16). The last congruence is exactly the stated image-sector condition.

First m >= 7. Indeed, reducing (1) modulo 512, the left side is 386+3m (mod 512), while the right side is 2^(2m+2)*322 (mod 512). For m=0,1,...,6, the respective pairs (left residue, right residue) are

| m | left side | right side |
|---:|---:|---:|
| 0 | 386 | 264 |
| 1 | 389 | 32 |
| 2 | 392 | 128 |
| 3 | 395 | 0 |
| 4 | 398 | 0 |
| 5 | 401 | 0 |
| 6 | 404 | 0 |

so none can satisfy (1). Therefore 2^(2m+2) is divisible by 16384.

Now reduce (1) modulo 16384:

0 = 574+1024v+319+512u+3m+5 (mod 16384).

By v = 15+3u (mod 16),

1024v = 15360+3072u (mod 16384).

Consequently,

3m+3584u+16258 = 0 (mod 16384).

Since 7j+14025 = 3584u+16258, this is precisely

**3m+7j+14025 = 0 (mod 16384).**

The congruence j = 319 (mod 512) is immediate.

### The congruences imply image-family membership

Conversely, suppose

- j = 319 (mod 512);
- 3m+7j+14025 = 0 (mod 16384).

Write j=319+512u. Reducing the second congruence modulo 512 gives

3m = 126 (mod 512),

hence m = 42 (mod 512). In particular m >= 42, so 16384 divides 2^(2m+2).

Set K=K(j,m). From (1), reduction modulo 16384 and the assumed congruence give

K = -j-3m-5 = 6j+14020 = 15934+3072u (mod 16384). (2)

The last residue is 574 modulo 1024. Thus K = 574 (mod 1024); since K is natural, there is v natural with K=574+1024v.

Substituting this into (2) yields

1024v = 15360+3072u (mod 16384),

so v = 15+3u (mod 16). Equivalently,

u+v = 15+4u (mod 16).

This is exactly membership in the second strict image family.

## Equivalent one-parameter residue form

For j=319+512u, the pullback congruence becomes

3m = 126-3584u (mod 16384).

Since 3 is invertible modulo 16384, this is equivalent to

**m = 42-6656u (mod 16384).**

Thus for each admissible j, there is exactly one residue class of m modulo 16384.

It follows that the parameter family has exact natural density

**1/(512*16384) = 1/2^23**

in the (j,m) lattice: one residue class for j modulo 512, and one residue class for m modulo 16384 for each such j.

## Disjointness from the earlier six/seven diagonal

The earlier diagonal requires

- j = 319 (mod 512);
- 3m = j+2879 (mod 4096).

The new congruence, reduced modulo 4096, gives

3m = -7j-14025 (mod 4096).

If both held, then 8j+16804 = 0 (mod 4096). But j = 319 (mod 512) forces

8j+16804 = 2972 (mod 4096),

a contradiction. The two parameter cylinders are disjoint.

## Exact pullback of the first strict family

The first strict family has the same affine target V(u,v), but with sector condition u+v = 0 (mod 4). Its exact high-stop pullback is the older diagonal:

- j = 319 (mod 512);
- 3m = j+2879 (mod 4096).

For the forward direction, the same small-m table above forces m>=7, so 4096 divides 2^(2m+2). Reducing the stopping identity modulo 4096 gives
0 = 898+1024v+512u+3m (mod 4096).
Since v+u = 0 (mod 4), this becomes 3m = -898+512u = j+2879 (mod 4096).

Conversely, suppose j=319 (mod 512) and 3m=j+2879 (mod 4096). Reducing modulo 512 gives 3m=126 (mod 512), hence m=42 (mod 512), so m>=42 and 4096 divides 2^(2m+2). The stopping identity then gives
K = -j-3m-5 = -2j-2884 = 574-1024u (mod 4096),
where j=319+512u. Thus K=574 (mod 1024), so K=574+1024v for some natural v; the stronger congruence modulo 4096 gives v+u=0 (mod 4). This recovers the first strict family.

## Combined parameter coverage with the first strict family

The first strict sixth/seventh family pulls back to the older diagonal

- j = 319 (mod 512);
- 3m = j+2879 (mod 4096).

For each admissible j, invertibility of 3 modulo 4096 gives one residue class of m modulo 4096, hence four residue classes modulo 16384. The new family gives one residue class modulo 16384 for each such j, and the disjointness proof above shows that it is not one of those four.

Thus the union of the two source-image exclusions covers exactly five of the 16384 possible m-classes for each j = 319 (mod 512), for total parameter density

**5/(512*16384) = 5/2^23.**

Conditioning on the common base cylinder j = 319 (mod 512), m = 42 (mod 512), there are 32 possible m-classes modulo 16384 for each fixed j-class. The old diagonal removes four of these, the new family removes one disjoint class, and exactly 27 of 32 classes remain outside these two exclusions. Those 27 classes are residual candidates, not evidence of halting.

This is only a density in the (j,m) parameter lattice; it is not a fraction of halting machines or of all high-stop states.

## Verification boundary

The underlying second strict sixth/seventh image theorem and its all-time exclusion from the genuine blank-root section orbit are original-source Lean certified by CI 43300420208, with no sorryAx.

The equivalence is now also formalized as s3_image_pullback_iff_congruence and highAllowedAllS3_iff_congruence in CSixSeventhC58.lean. Both the C58 high predicate and the latest six-sector high predicate in CSixSeventhSixAll.lean now use the direct congruence form; the exact halting-iff wrappers convert a congruence witness back to image coordinates only when applying the all-time root exclusion. These additions are an unverified Lean proof draft: no fresh original-source CI audit has run on them. The surrounding C58 and SixAll source-composition wrappers still require a fresh successful original-source audit. This note does not promote that pending integration to a certified Machine C exclusion, and it does not decide Machine C or BB(6).
