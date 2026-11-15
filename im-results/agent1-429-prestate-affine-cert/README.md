# Last-reset prestate affine inverse sieve (candidate)

**Status:** computational candidate; the combined extension has not yet been Lean-checked. Do not cite the 2,192 exclusions as a theorem until the added root lemmas are incorporated into a Lean certificate and compiled.

## Purpose

The terminal-state parameterization loses useful information about the last-reset prestate. This experiment applies the existing inverse-kernel certificate to the prestate itself, retaining the quotient in the branch parameter d.

For branch 9 use c=10,C=25; for branch 10 use c=6,C=21. The exact source-derived equations are

[
x=2^n(d+c)+rac{2d-3n-C}{4},qquad y=2(x-d)+1.
]

For a residue class d=Mq+r, the affine family (x,y)=(Aq+a,Bq+b) is

[
A=M2^n+M/2,quad
a=2^n(r+c)+(2r-3n-C)/4,
]
[
B=M(2^{n+1}-1),quad b=2(a-r)+1.
]

The base-counter term is important: the first term 2^n(r+c) is **not** divided by four. An earlier audit made that mistake; its short-burst counts were withdrawn and corrected in the Agent 6 mailbox.

## Long-burst audit

The current d-residues.json supplies 44 classes (n mod 32, d mod 16). Refining each to n mod 256, d mod 128 gives 64 affine families per class, 2,816 in total. Since n>=18, the 2^n term vanishes in the moduli used by the root constraints; the representative n is chosen at least 18 while preserving n mod 256.

The JS audit evaluates the depth-14 inverse certificate with:
- the eight existing Bad conditions from BB429InverseKernelExtended;
- the odd/odd root-row table, strengthened by the two-step exclusion (a mod 16,b mod 8)=(9,5);
- BB429RootMod32.rooted_not_5_1;
- BB429RootMod64R0.no_1_25, no_1_23, and no_33_23;
- BB429RootMod64R2.no_9_9.

The JSON file stores every surviving pair (n mod 256,d mod 128), grouped by the original 44 classes.

| Quantity | Count |
|---|---:|
| Affine families tested | 2,816 |
| cert 14 accepted as unreachable | 2,192 |
| Remaining candidate families | 624 |

The 16 classes with zero survivors are:
[
(3,5),(5,10),(7,7),(7,11),(11,1),(13,6),(15,3),(15,7),
(19,13),(21,2),(23,3),(23,15),(27,9),(29,14),(31,11),(31,15).
]

The other 28 classes retain 16–32 of their 64 lifts each. See long-burst-mod256-128.json for the exact survivor pairs and per-class counts.

## Required formalization

1. Compile the new root lemma Reach a b -> not (a mod 16=9 and b mod 8=5) under a>=33, proved from odd_back and even_back.
2. Add the existing mod-32/mod-64 root lemmas to the affine Bad predicate with coefficient-divisibility guards.
3. Extend cert_sound for these additional Bad disjuncts.
4. Define the affine prestate family above in Lean and prove va s q=x, vb s q=y.
5. Reproduce the 2,816 Boolean evaluations with Lean decide/native_decide and derive the corresponding d-family exclusions.

The 624 surviving affine families are only a reduced search space, not evidence that any one is actually root-reachable.
