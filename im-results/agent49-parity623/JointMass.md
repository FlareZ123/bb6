# Tight joint-mass bound for the #623 B-drain

**Agent 49, 2026-11-07. Local exact-model proof complete; pinned source CI pending.**

Let B(a,b,d) denote the authentic recursive drainB map from the pinned
Cryptids machine source. If

[
b<3^n,qquad B(a,b,d)=operatorname{some}(D(a',d')),
]

then the proposed sharp bound is

[
oxed{a'+d'le a+d+3b+3n+1.}
]

The source proof is in JointMassSource.lean. The same induction was compiled
locally in Lean 4.36.0-rc2 against a minimal model whose evalA and drainB
equations are copied verbatim from the pinned source. The source-import
verification is being run through the repository's pinned CI workflow.

## Evaluator lemmas

For an evaluator call E(a,k,m)=some(a',b',d') with k<3^n, split on the
residual block count b'.

### Positive residual block

If b'>0, there are r,s with

[
r+s=n,qquad r>0,qquad b'<3^s,
]
[
a'+d'+3b'le a+m+k+r.
]

The induction on n splits k=3q+j:
- j=0 and a>0: evalA returns (a-1,q,m+2), so choose r=1,s=n-1.
- j=2: evalA returns (a+1,q,m), again choose r=1,s=n-1.
- j=1 and a=0: evalA returns (0,q,m), again choose r=1,s=n-1.
- j=1 and a>0: recurse on (a-1,q,m+2q+3), then lift the recursive r by one.
The n=0 case is impossible when b'>0.

### Zero residual block

If b'=0, the positive-depth potential is too strong. The separate bound is

[
a'+d'le a+m+k+n+1.
]

This is proved by induction on n. The recursive digit-1 case is exact under
the induction hypothesis; the direct digit-0, digit-2 and a=0 cases close
arithmetically. This split is essential: for example,
E(2,1,0)=(0,0,5), so the positive-residual inequality cannot be extended to
b'=0 with the same r+s=n potential.

## Drain induction

For b=0, drainB returns D(a,d), and the target inequality is immediate.

For b>0, write the first evaluator result as (a1,b1,d1), with input
(a,b-1,d+2b+3). The evaluator lemmas apply because b-1<3^n.

- If b1=0, the zero-residual bound gives
  a1+d1 ≤ a+d+3b+n+3 ≤ a+d+3b+3n+1, since n>0.
- If b1>0, choose r,s with r+s=n and r>0. Then b1<3^s, so strong
  induction applies to the remaining drain:
  a'+d' ≤ a1+d1+3b1+3s+1
  ≤ a+d+3b+3+r+3s
  ≤ a+d+3b+3n+1.

## Sharpness

Define B_0=2 and B_(n+1)=3B_n+1. The existing source theorem
drainB_sharp_witness proves

[
B(n+2,B_n,d)=D(0,d+3B_n+4(n+1)+2).
]

Also B_n<3^(n+1). Taking the depth parameter N=n+1, the output mass is

[
d+3B_n+4n+6
=(n+2)+d+3B_n+3(n+1)+1,
]

so equality holds in the joint-mass bound for every n,d. The coefficient
3n+1 is therefore sharp uniformly.

## Relevance to the root-ray program

The earlier independent component bounds permit a weaker sum estimate.
This theorem preserves correlation between the first and third counters and
reduces the universal drain overhead. It can tighten the terminal mass
thresholds used in the #623 root-ray analysis. It does not by itself prove
that the blank-root orbit avoids every terminal ray.
