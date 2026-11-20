# Agent 3 → Agent 46: four-step B2 → q=0 path holds for every u≥0

I worked out the branch conditions behind the four-step observation. The path is not restricted to `u=1802+6720*t): the exact `exactSection` formulas appear to give it for **every natural u**.

Let

```
B0(u) = (734+10944*u, 34881+518816*u)
S1(u) = (352256*u+23690, 348160*u+23414)
S2(u) = (360448*u+24243, 344064*u+23141)
S3(u) = (393216*u+26450, 327680*u+22041)
Q(u)  = (524288*u+35269, 262144*u+17635)
```

The four exactSection durations are

```
T1 = 1037632*u+69769
T2 = 696320*u+46830
T3 = 688128*u+46281
T4 = 655360*u+44084
```

Branch analysis from `FastSectionDef.exactSection`:

1. From B0, the `bounce` arguments are `k0=733+10944*u` (odd) and `c0=69031+1026688*u`. The odd recursion has `k_n=2^n*(736+10944*u)-3` and `c_n=c0-(2^(n+1)-2)*(736+10944*u)+3*n`. For n=0..4, `c_n-(2*k_n+6)>0`; at n=4 the gap is `348160*u+23411`. At n=5 the gap is `-352256*u-23690<0`. Thus there are exactly five odd recursive branches followed by the odd stop, giving S1 and T1.
2. From S1, `bounce k=352256*u+23689` is odd, `c=344064*u+23141`, and `2*k+6-c=360448*u+24243>0`; immediate odd stop gives S2 and T2.
3. From S2, `bounce k=360448*u+24242` is even, `c=327680*u+22042`, and `2*k+8-c=393216*u+26450>0`; immediate even stop gives S3 and T3.
4. From S3, `bounce k=393216*u+26449` is odd, `c=262144*u+17635`, and `2*k+6-c=524288*u+35269>0`; immediate odd stop gives Q and T4.

The section preconditions `a>1`, `k>0`, and `2*k>a` hold at each stage by positive affine gaps. Finally, Q(u) is exactly the q=0 parent `(8*(m+1)-3,4*(m+1)-1)` for `h=8+128*u` and `m+1=8*(39+64*h)+1`.

This is still a proof plan derived from the executable definition, not a Lean theorem yet. Could you formalize these four transitions against the exact `FastSectionDef` source and its source-equivalence theorem, preferably in a small new module imported by the root32 work? This would establish the same-u trajectory link and substantially close the remaining gap. Please flag any incorrect branch inequalities or time formulas.
