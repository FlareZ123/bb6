# Agent 47 — CLine inverse-tree audit and forward-prefix bound

**Status:** intermediate computational/algebraic research. This directory is not a publishable result and does not claim a solution of Machine C or BB(6).

## 1. Thin-gateway inverse tree: exact branch correction

The gateway family in Agent11's `CLine` is
[
T_j=(0,2j,4j+10).
]
The high inverse parents derived in Agent13's `ThinGatewayInverse.md` are
[
Q_{j',m}=
left(2j'+3,;2^{2m+2}(j'+3)-j'-3m-5,;0ight),
qquad j+2=4^m(j'+3).
]

There is one additional original-source predecessor case that must be retained. At an even inverse depth (2m), when the recurrence reaches (K_{2m}=4), the chain contains ((2,2,C_{2m}+2)) with odd third coordinate. It has a predecessor from the special ((1,k+1,0)mapsto(2,2,2k+1)) clause. This gives
[
j=2^{2m+3}-2,qquad
(1,2^{2m+5}-3m-7,0),
]
which is exactly the low stopping family with low parameter (m+1). Thus the complete gateway reduction must allow both high-family parents and this low-family parent. See the two dated Agent13 mailbox notes:
- `communications/agent13/20261117T1440Z_agent47-inverse-tree-low-branch.md`
- `communications/agent13/20261117T1445Z_agent47-full-predecessor-split.md`

These are algebraic predecessor analyses, not yet a Lean theorem.

## 2. Exact forward orbit, compressed by maximal high runs

The deterministic `CLine.nextC` orbit starts at ((5,0,1)). On states with (age1,cge4), one ordinary step is
[
(a,k,c)mapsto(a-1,k+1,c-1).
]
A maximal run of this branch of length (n=min(a,c-3)) lands at either (a=0) or (c=3). The script `forward_prefix.js` uses a boundary macro:
1. apply one exact `nextC` transition from a boundary state ((a=0) or (cle3));
2. if the result is in the high branch, skip the maximal high run using the closed form above;
3. repeat.

Every macro endpoint is a boundary state. Every thin gateway has (a=0), and every interior state of a skipped high run has (a>0); therefore checking macro endpoints checks every possible thin gateway on the exact orbit.

### Reproduced run

Target rank: (8cdot1{,}000{,}000+10=8{,}000{,}010).

| Quantity | Value |
|---|---:|
| Ordinary `nextC` transitions represented | 2,285,059,257,097 |
| Boundary macro transitions | 4,571,232 |
| High-branch transitions collapsed | 2,285,054,685,865 |
| Macro endpoints with (a=0) | 1,143,020 |
| Thin-gateway hits | 0 |
| Final state | ((5{,}079{,}022,;1{,}460{,}493,;3)) |
| Final rank (a+2k+c) | 8,000,011 |
| Rolling endpoint checksum (FNV-1a, 32-bit) | `a11c234b` |

The source theorem `rank_mono` in `im-results/agent11-c-line/CLine.lean` establishes that rank is nondecreasing under every ordinary transition. Since (operatorname{rank}(T_j)=8j+10), this computation excludes every (T_j) with (0le jle1{,}000{,}000): none occurred in the checked prefix, and every later state has rank at least 8,000,011.

The M512 thin-gateway residue set in `im-results/agent13-residual-frontier/ThinGatewayM512.md` has residue 66 as its first surviving lift above this finite bound, namely (j=1{,}000{,}002). That is the first M512-admitted gateway not eliminated by this forward-prefix result; it remains open here.

**Evidence status:** the JS simulation is exact and reproducible, but this 4.57-million-macro-step prefix has not yet been kernel-checked in Lean. A formal proof should prove the high-run closed form, prove that the boundary macro preserves reachability and covers every reachable (a=0) state, then verify the finite macro orbit and combine it with `rank_mono`. Do not describe the finite bound as a proof that no gateway exists.
