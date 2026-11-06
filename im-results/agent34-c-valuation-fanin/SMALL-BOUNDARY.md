# Machine C: all small-right output fibres and valuation bounds

The full source-image iff in [Agent 3's SectionAllInverse.lean](../agent3-c-bounce-inverse/SectionAllInverse.lean) covers the exceptional source and all recursive depth cases. The earlier [valuation-fanin synthesis](README.md) handles all outputs y>=5. Here is the complementary complete low-y analysis. These count bounds are **paper derivations from a source-certified iff**; the independent all-parameter count is not yet a Lean theorem. Machine C and BB(6) remain open.

## Exact fibres when y is 0, 1, or 2

No original section transition outputs y=0. The sole y=1 output is (5,1) from (1,0). For every x>=0, the y=2 target (x,2) has the unique source (x+2,0). These follow by exhausting the source-if-and-only-if branches.

## y=3, valuation of x+6

Every y=3 output has even x, including the special (2,3) from (1,1). Any ordinary high-source edge must have **odd source first counter** a>=3 and satisfy

```text
x+6 = 2^(n+1)*(a+3)
2*k+a+3*n = x+1
n even, 0<=n<=v2(x+6)-2.
```

Each n determines at most one pair (a,k). The source-level depth and parity restrictions are proved in [ValuationSmall.lean](ValuationSmall.lean), from the exact original-source preimage iff. The only additional possible a=1 high source has x+6=16*2^n, with n odd. Hence it can exist only if x+6 is a pure power of 2, with v=v2(x+6) odd and >=5. In that exceptional case the high a>=3 constraint sharpens n<=v-4, leaving at most floor(v/2)-1 high-depth choices; adding the exceptional parent recovers floor(v/2). The isolated source (1,1) for (2,3) is its unique parent by the same grammar.

**Sharp global count bound:**

```text
d(x,3) <= floor(v2(x+6)/2)    for every x>=0.
```

This is attained for **every v>=2** at x=3*2^v-6: every even n between 0 and v-2 gives a distinct genuine odd-a high source, with a(n)=3*2^(v-n-1)-3 and k(n)=(x+1-a(n)-3*n)/2. Each source obeys a>=3, k>=1, a<2*k.

## y=4, valuation of x+4

Every (x,4) has a direct source (x+2,1). An exceptional source (0,1) also produces (0,4). Other zero-first sources require x+4=8*2^n with n odd; there can be at most one. The high-input sources must have **even first counter** a>=2 and satisfy

```text
x+4 = 2^(n+1)*(a+2)
2*k+a+7+3*n=x+8
n odd, 0<=n<=v2(x+4)-2.
```

The high-depth restriction follows directly from [ValuationSource.lean](ValuationSource.lean), which applies at y=4 too. Odd-a high bounces cannot output four, by the complete source grammar.

For x even, putting v=v2(x+4), the count is at most floor(v/2)+1. If v is even, at most v/2-1 odd depths plus direct and one exceptional source occur. If v is odd, at most (v-1)/2 odd depths and the direct source occur. For x odd, only the direct source is possible. The bound is attained for **every v>=2** at x=2^v-4 when v is even, or x=3*2^v-4 when v is odd. The smallest case x=0 has the two sources (2,1) and (0,1).

## A uniform degree budget for every output

For y>=4, define Q=x+y if x+y is even, otherwise Q=x+y+1. For y=3, define Q=x+6. Then, without any assumption of blank reachability,

```text
y >= 3  implies d(x,y) <= floor(v2(Q)/2)+1.
y = 3   improves to d(x,3) <= floor(v2(x+6)/2).
y = 2   has d(x,2)=1; y=1 has d(5,1)=1 only; y=0 has d=0.
```

The bound for y>=4 is sharp for every valuation v>=2 already on y=4, and for every v>=3 on the y>=5 families in README.md.

[low_y34.py](low_y34.py) implements the original section interpreter separately from the complete arithmetic candidate grammar. Its regression passed 122,500 source pairs; 200,000 low-boundary targets x<100000; and all displayed sharpness examples for v=2..18. The mathematical proof uses the all-input source iff, while finite tests detect accidental implementation or algebra errors.

The stronger y=3 valuation-depth theorem is source-connected in the project manual CI workflow; no new machine-wide halting decision follows.
