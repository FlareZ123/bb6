# Exact parameter congruence for the second strict image family

## Statement

Let
\[
K(j,m)=2^{2m+2}(j+3)-(j+3m+5).
\]
The second strict sixth/seventh image family is
\[
V(u,v)=(641+1024u,\;574+1024v),\qquad
(u+v)\bmod16=(15+4u)\bmod16.
\]

Its exact pullback through the original high-stop equation is
\[
\boxed{
j\bmod512=319,\qquad
(3m+7j+14025)\bmod16384=0.
}
\]
For all natural \(j,m\), this is equivalent to the existence of \(u,v\in\mathbb N\) satisfying
\[
j=319+512u,\quad K(j,m)=574+1024v,\quad
(u+v)\bmod16=(15+4u)\bmod16.
\]

In particular, the pullback forces \(m\bmod512=42\), hence \(m\ge42\). No separate \(m\ge7\) hypothesis is needed in the final parameter description.

## Proof

Write \(P=2^{2m+2}(j+3)\). The elementary bound
\[
j+3m+5\le 2^{2m+2}(j+3)
\]
holds for all \(j,m\), so
\[
K+j+3m+5=P. \tag{1}
\]

Suppose first that \(j=319+512u\), \(K=574+1024v\), and \(v\equiv15+3u\pmod{16}\). The last congruence is exactly the image-sector condition.

First \(m\ge7\). Reducing (1) modulo \(512\), the left side is \(386+3m\pmod{512}\), while the right side is \(2^{2m+2}\cdot322\pmod{512}\). For \(m=0,1,\ldots,6\), the respective pairs (left residue, right residue) are
\[
(386,264),(389,32),(392,128),(395,0),
(398,0),(401,0),(404,0),
\]
so none can satisfy (1). Thus \(16384\mid2^{2m+2}\).

Reducing (1) modulo \(16384\) now gives
\[
0\equiv574+1024v+319+512u+3m+5.
\]
Since \(v\equiv15+3u\pmod{16}\),
\[
1024v\equiv15360+3072u\pmod{16384}.
\]
Therefore
\[
3m+3584u+16258\equiv0\pmod{16384}.
\]
But \(7j+14025=3584u+16258\), giving the claimed congruence. The condition \(j\equiv319\pmod{512}\) is immediate.

Conversely, suppose
\[
j\equiv319\pmod{512},\qquad
3m+7j+14025\equiv0\pmod{16384}.
\]
Write \(j=319+512u\). Reducing the second congruence modulo \(512\) gives
\[
3m\equiv126\pmod{512},
\]
hence \(m\equiv42\pmod{512}\). In particular \(m\ge42\), so \(16384\mid2^{2m+2}\).

Set \(K=K(j,m)\). From (1), reduction modulo \(16384\) and the assumed congruence give
\[
K\equiv-j-3m-5
 \equiv6j+14020
 \equiv15934+3072u
 \pmod{16384}. \tag{2}
\]
The last residue is \(574\pmod{1024}\). Thus \(K\equiv574\pmod{1024}\); since \(K\in\mathbb N\), there is \(v\in\mathbb N\) with
\[
K=574+1024v.
\]
Substituting this into (2) yields
\[
1024v\equiv15360+3072u\pmod{16384},
\]
so \(v\equiv15+3u\pmod{16}\). Equivalently,
\[
u+v\equiv15+4u\pmod{16}.
\]
This is exactly membership in the second strict image family.

## Equivalent one-parameter residue form

For \(j=319+512u\), the pullback congruence becomes
\[
3m\equiv126-3584u\pmod{16384}.
\]
Since \(3\) is invertible modulo \(16384\), this is equivalent to
\[
\boxed{m\equiv42-6656u\pmod{16384}.}
\]
Thus for each admissible \(j\), there is exactly one residue class of \(m\) modulo \(16384\).

It follows that the parameter family has exact natural density
\[
\frac1{512\cdot16384}=\frac1{2^{23}}
\]
in \(\mathbb N^2\): one residue class for \(j\) modulo \(512\), and one residue class for \(m\) modulo \(16384\) for each such \(j\).

## Disjointness from the earlier six/seven diagonal

The earlier diagonal requires
\[
j\equiv319\pmod{512},\qquad
3m\equiv j+2879\pmod{4096}.
\]
The new congruence, reduced modulo \(4096\), gives
\[
3m\equiv-7j-14025\pmod{4096}.
\]
If both held, then \(8j+16804\equiv0\pmod{4096}\). But \(j\equiv319\pmod{512}\) forces
\[
8j+16804\equiv2972\pmod{4096},
\]
a contradiction. The two parameter cylinders are disjoint.

## Combined parameter coverage with the first strict family

The first strict sixth/seventh family pulls back to the older diagonal
[
j\equiv319\pmod{512},\qquad
3m\equiv j+2879\pmod{4096}.
]
For each admissible (j), invertibility of (3) modulo (4096) gives one residue class of (m) modulo (4096), hence four residue classes modulo (16384). The new family gives one residue class modulo (16384) for each such (j), and the disjointness proof above shows that it is not one of those four. Thus the union of the two source-image exclusions covers exactly five of the (16384) possible (m)-classes for each (j\equiv319\pmod{512}), for total parameter density
[
rac{5}{512\cdot16384}=rac5{2^{23}}.
]
This is only a density in the ((j,m)) parameter lattice; it is not a fraction of halting machines or of all high-stop states.

## Verification boundary

The underlying second strict sixth/seventh image theorem and its all-time exclusion from the genuine blank-root section orbit are original-source Lean certified by CI 43300420208, with no sorryAx.

The equivalence is now also formalized as s3_image_pullback_iff_congruence and highAllowedAllS3_iff_congruence in CSixSeventhC58.lean. Both the C58 high predicate and the latest six-sector high predicate in CSixSeventhSixAll.lean now use the direct congruence form; the exact halting-iff wrappers convert a congruence witness back to image coordinates only when applying the all-time root exclusion. These additions are an unverified Lean proof draft: no fresh original-source CI audit has run on them. The surrounding C58 and SixAll source-composition wrappers still require a fresh successful original-source audit. This note does not promote that pending integration to a certified Machine C exclusion, and it does not decide Machine C or BB(6).
