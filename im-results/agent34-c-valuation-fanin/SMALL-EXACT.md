# Complete closed-form source indegree at y=3 and y=4

This refines the sharp bounds in [SMALL-BOUNDARY.md](SMALL-BOUNDARY.md) to exact, all-input source counts. It is a **written mathematical derivation using Agent3's already kernel-certified full source preimage iff**, not a separate Lean proof of the global cardinality. No BB(6) or machine blank halting statement follows.

Write d(x,y) for the number of distinct nonnegative source pairs (a,k) satisfying the original section equality secNext(a,k)=some(x,y), and v2(q) for the exponent of two dividing positive q. Let I(P) be 1 if P and 0 otherwise.

**Exact right-three formula, all x>=0:**

```text
q=x+6,  v=v2(q).
d(x,3) = floor(v/2) - I(q is a power of 2 and v is even and v>=4).
```

It is zero for odd x. To prove the formula, by the complete source iff, every ordinary high predecessor is indexed by an **even depth** n with 0<=n<=v-2; its coordinates are

```text
a(n)=q/2^(n+1)-3
k(n)=(x+1-a(n)-3*n)/2.
```

When the odd factor q/2^v is at least three, all floor(v/2) even depths have a>=3, k>=1, a<2*k, hence are valid and distinct. If q=2^v, the a>=3 requirement instead forces n<=v-4, losing one depth. For odd v>=5 that loss is exactly restored by the single a=1 high predecessor with n=v-4. At v=3, q=8 (x=2), the unique source is the special (1,1); no high a>=3 source exists. For even v>=4, the exceptional a=1 source is parity-impossible, leaving floor(v/2)-1. At v<=1 there are no source branches. This proves the displayed formula including small exceptions.

**Exact right-four formula, all x>=0:**

```text
If x is odd: d(x,4)=1.
If x is even: q=x+4, v=v2(q).
  v even: d(x,4)=v/2 + I(q is a power of 2).
  v odd:  d(x,4)=(v+1)/2 - I(q is a power of 2).
```

The direct source (x+2,1) always exists. For even x, every further ordinary source is high and even, indexed by an **odd n** in 1<=n<=v-2, with

```text
a(n)=q/2^(n+1)-2
k(n)=(x+1-a(n)-3*n)/2.
```

When q/2^v>=3, each permitted depth gives exactly one valid high source. When q=2^v, the a>=2 guard forces n<=v-3, deleting one high odd depth only if v is odd. A single zero-first high source is available precisely when q is a power of two with even v>=4, restoring one additional parent; the special (0,1) at x=0, v=2 supplies the same extra source. For odd x, q=x+4 is odd and all bounce exits to y=4 are impossible, leaving the direct source. All guards follow directly by substitution into the certified inverse iff, including the strictly positive high-branch cost and 2*k>a condition.

Both formulas have **unbounded sharp families**: for y=3, q=3*2^v gives d=floor(v/2) for every v>=2; for y=4, q=2^v with even v>=2, or q=3*2^v with odd v>=3, gives d=floor(v/2)+1. The formulas have passed independent forward/inverse regression for all 0<=x<100000, in addition to explicit high-valuation examples. These finite checks validate the implementation but do not prove the formulas.

For source-level kernel-certified depth/branch control, consult [ValuationSmall.lean](ValuationSmall.lean) and [ValuationSource.lean](ValuationSource.lean), checked by [CI 42201145636](https://github.com/FlareZ123/bb6/actions/runs/42201145636). A stand-alone formal counting theorem in Lean remains useful future work.
