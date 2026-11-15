# Last-reset prestate affine inverse sieve (candidate)

**Status:** computational candidate; the combined extension has not yet been Lean-checked. Do not cite the 2,192 exclusions as a theorem until the added root lemmas are incorporated into a Lean certificate and compiled.

## Purpose

The terminal-state parameterization loses useful information about the last-reset prestate. This experiment applies the existing inverse-kernel certificate to the prestate itself, retaining the quotient in the branch parameter d.

For branch 9 use c=10,C=25; for branch 10 use c=6,C=21. The exact source-derived equations are:

```
x = 2^n*(d+c) + (2*d - 3*n - C)/4
y = 2*(x-d) + 1
```

For a residue class d=M*q+r, the affine family (x,y)=(A*q+a,B*q+b) is:

```
A = M*2^n + M/2
a = 2^n*(r+c) + (2*r - 3*n - C)/4
B = M*(2^(n+1)-1)
b = 2*(a-r)+1
```

The base-counter term is important: the first term 2^n*(r+c) is **not** divided by four. An earlier audit made that mistake; its short-burst counts were withdrawn and corrected in the Agent 6 mailbox.

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
```
(3,5),(5,10),(7,7),(7,11),(11,1),(13,6),(15,3),(15,7),
(19,13),(21,2),(23,3),(23,15),(27,9),(29,14),(31,11),(31,15)
```

The other 28 classes retain 16–32 of their 64 lifts each. See long-burst-mod256-128.json for the exact survivor pairs and per-class counts.

## Iterated d-modulus refinement

Starting from the 624 survivors at M=128, split each residue into its two lifts and reapply the same depth-14 certificate. The JS port gives:

| d modulus M | total families | survivors |
|---:|---:|---:|
| 128 | 2,816 | 624 |
| 256 | 5,632 | 814 |
| 512 | 11,264 | 1,212 |
| 1,024 | 22,528 | 1,603 |
| 2,048 | 45,056 | 2,412 |
| 4,096 | 90,112 | 3,183 |
| 8,192 | 180,224 | 4,787 |
| 16,384 | 360,448 | 6,349 |
| 32,768 | 720,896 | 9,559 |

Thus the surviving density falls from 22.2% at M=128 to 1.33% at M=32,768. The absolute number of survivors grows; this is a sparse 2-adic sieve, **not** a finite closure or proof that no long-burst prestate exists.

For the 2,816 M=128 families, the computed Boolean outcome was unchanged when the representative n was shifted by each of 256, 512, 768, 1,024, 2,048, ..., 131,072. This is useful evidence for a small n-period, but is not a proof of uniformity in n. A Lean proof should establish the exact period rather than rely on these samples.

## Required formalization

1. Compile the new root lemma Reach a b -> not (a mod 16=9 and b mod 8=5) under a>=33, proved from odd_back and even_back.
2. Add the existing mod-32/mod-64 root lemmas to the affine Bad predicate with coefficient-divisibility guards.
3. Extend cert_sound for these additional Bad disjuncts.
4. Define the affine prestate family above in Lean and prove va s q=x, vb s q=y.
5. Reproduce the 2,816 Boolean evaluations with Lean decide/native_decide and derive the corresponding d-family exclusions.

The 624 surviving affine families are only a reduced search space, not evidence that any one is actually root-reachable.


The 28 nonempty classes have survivor counts in {16,24,28,32}; each of the 16 empty classes is fully certified. Across all 2,816 trees, the JS traversal reaches at most inverse depth 6, at most 14 nodes, and at most 9 accumulated powers of two in the affine denominator. This is small enough that a Lean finite replay should be practical; the key work is proving the extended Bad clauses sound.
