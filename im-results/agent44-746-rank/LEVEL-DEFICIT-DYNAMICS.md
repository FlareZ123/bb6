# Level-deficit dynamics of the #746 blank-root chain

## Scope and status

This is an intermediate structural reduction for the blank-root trajectory studied in [the 100,000-transition report](../agent10-cascade/ROOT-3ADIC-COVERAGE-100K.md). It does **not** prove that the root never reaches a fatal state, eliminate the #746 machine, or determine (BB(6)).

The source-level Lean development is in [`LevelDeficitDynamics.lean`](LevelDeficitDynamics.lean). It formalizes the even-deficit halving and level-exit criteria, persistence of earlier sweep guards under an odd reset, the odd-offset factorization, and the odd-output equation. The selective original-source CI run is currently pending; do not treat the Lean proof as verified until that run succeeds and its axiom output contains no `sorryAx`.

## 1. Level coordinate and even reset

Write (p=2^K). A height (h) at first-failure level (K) satisfies
[
  orall j<K,quad 8cdot2^jle h+j+5,
  qquad h+K+5<8cdot2^K.
]
Use the level deficit
[
  D_K(h)=8cdot2^K+K-h.
]

On an even reset,
[
  u=4cdot2^K+rac{h+K}{2}.
]
The exact identity is
[
  2u=8cdot2^K+h+K,
  qquad D_K(u)=rac{D_K(h)}2.
]
The reset remains at level (K) precisely when (D_K(h)>4K+10). If (D_K(h)le4K+10), the next first-failure level is exactly (K+1). These are arithmetic statements about the reset map; interpreting the even map as an actual machine transition also requires that the current state is not already the fatal equality (h+K+4=4cdot2^K).

This gives a simple exact criterion for the parity of a whole level exit. Suppose a nonfatal level entry has
[
  D_{m in}=2^e r,qquad r 	ext{odd}.
]
Repeated same-level even resets halve the deficit. If (e=0), the odd branch is taken immediately. If (ege1), the last possible same-level even state before reaching the odd residual is (2r):
- if (r>2K+5), then (2r>4K+10), so the even reset from (2r) stays at level (K), leaving the odd residual (r); the level exits by the odd branch;
- if (rle2K+5), then (2rle4K+10), so the first dyadic residual at or below the threshold is even and its reset exits to level (K+1).

Consequently, for a nonfatal entry, the level exits oddly iff
[
  e=0quad	ext{or}quad r>2K+5.
]
The root report's observed terminal residual bound (D_{m exit}>4K+10) for the first 100,000 transitions is stronger than this criterion, but remains finite computational evidence.

## 2. Odd reset: the 2-adic offset is the reset exponent

At an odd exit, let
[
  P_K=4cdot2^K+leftlfloorrac{h+K}{2}ightfloor+3
]
be the odd-reset parameter. The source inverse-band theorem gives
[
  6cdot2^K+1le P_Kle8cdot2^K-1.
]
Write (P_K=2^t d), with (d) odd, and define the complementary offset
[
  A_K=8cdot2^K-P_K.
]
Then
[
  1le A_Kle2^{K+1}-1,
  qquad D_{m exit}=2A_K+2K+5.
]
The key exact factorization is
[
  A_K=2^t a,qquad a 	ext{odd},
  qquad a+d=2^{K+3-t}.
]
In particular,
[
  oxed{t=v_2(A_K).}
]
Thus the exponent stripped from the odd-reset parameter is exactly the 2-adic valuation of the terminal-deficit offset. Also (tle K), since (2^tle A_K<2^{K+1}).

The child height is
[
  h'=rac{3^{t+1}d-5}{2},
  qquadoxed{2h'+5=3^{t+1}d}.
]
Combining the two equations gives a mixed 2-adic-to-3-adic cocycle:
[
  A_K=2^t a,quad a+d=2^{K+3-t}
  quadlongmapstoquad
  2h'+5=3^{t+1}d.
]
The precision of the next entry's 3-adic affine-height coordinate is therefore controlled by the 2-adic valuation of the previous level's offset (with any additional valuation coming from (d)).

The child remains beyond the old sweep: its first-failure level (K') is strictly greater than (K). Its next entry deficit is the affine expression
[
  D_{m in}'=8cdot2^{K'}+K'-h'
  =rac{16cdot2^{K'}+2K'+5-3^{t+1}d}{2}.
]
This last identity is an immediate algebraic consequence of the checked odd-output equation and the definition of deficit.

## 3. Exact fatal-hit equation and inverse parameterization

Let
[
  F_n=4cdot2^n-n-4
]
be the fatal height at level (n), and put
[
  G(n)=2F_n+5=8cdot2^n-2n-3.
]
An odd child (h') is fatal at its next level (K'=n) iff
[
  oxed{3^{t+1}d=G(n).}
]
Hence a necessary target-side condition is
[
  3^{t+1}mid G(n).
]
But this 3-adic divisibility condition is not sufficient: the source dyadic band must also hold. In terms of the odd-reset parameter,
[
  P_K=2^t d=rac{2^tG(n)}{3^{t+1}},
  qquad
  6cdot2^K+1le P_Kle8cdot2^K-1.
]
For fixed ((n,t)), these dyadic bands are disjoint as (K) varies, so there is at most one possible source level (K). If it exists, the source height is forced by
[
  h=2P_K-8cdot2^K-K-5.
]
Equivalently, in offset coordinates,
[
  a=2^{K+3-t}-rac{G(n)}{3^{t+1}},
]
which must be an admissible positive odd integer and must equal the root's actual (a).

This is a precise forward/inverse intersection problem: the root supplies ((K,t,a)), while a fatal target supplies ((n,t,G(n)/3^{t+1})). A 3-adic selector can identify candidate target indices, but the exact 2-adic offset match and the dyadic source band remain essential.

A small root example illustrates why the target-side divisibility alone is weak. At (K=4), the root has (D_{m exit}=73), (A=30=2cdot15), (t=1), (a=15), and (d=49), so (h'=218) at (K'=5). Here (G(5)=243=3^5), so the target-side condition (9mid G(5)) passes. But a fatal child at (n=5) would require (d=243/9=27), giving (P=54), outside the source band ([97,127]) at (K=4). The actual (d=49) is not the fatal value.

## 4. Relationship to the Q-index / Q-depth selectors

The Q-index and Q-depth selectors describe inverse-coordinate divisibility for the #746 (t=1) parent-candidate locus. They are not, by themselves, a parameterization of the entire blank-root level-entry sequence. The new forward identity supplies a possible bridge: a root odd reset with exponent (t=1) produces an entry with (2h'+5=9d); if that entry is independently identified as the parent (q) in the source identity (Q_j(n)=9(2q+5)), then (Q_j(n)=81d). More generally, the root's (t) controls the 3-adic depth of (2h'+5), while the Q selectors describe a separate index/depth coordinate.

The missing step is to identify, from the actual root trajectory, when a child entry is one of those Q-parent heights and what its even depth (j) is. No global identification (j=K') (or any other fixed formula) is established here. The exact fatal-hit equation above is the safer bridge to use until that parent/depth alignment is proved.

See [Q-index / Q-depth selector duality](Q-INDEX-DEPTH-DUALITY.md) for the existing inverse-coordinate result.

## 5. Initial root examples

The following values are computed from the blank-root recurrence. (D_{m in}) is the level-entry deficit; (D_{m exit}) is the residual after same-level even resets. The (a,d,t) columns apply to odd exits.

| (K) | (D_{m in}) | even resets | (D_{m exit}) | (A) | (t) | (a) | (d) | (K') | (D_{m in}') |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 2 | 23 | 0 | 23 | 7 | 0 | 7 | 25 | 3 | 32 |
| 4 | 73 | 0 | 73 | 30 | 1 | 15 | 49 | 5 | 43 |
| 5 | 43 | 0 | 43 | 14 | 1 | 7 | 121 | 7 | 489 |
| 7 | 489 | 0 | 489 | 235 | 0 | 235 | 789 | 8 | 875 |
| 8 | 875 | 0 | 875 | 427 | 0 | 427 | 1621 | 9 | 1676 |
| 9 | 1676 | 2 | 419 | 198 | 1 | 99 | 1949 | 11 | 7627 |
| 11 | 7627 | 0 | 7627 | 3800 | 3 | 475 | 1573 | 13 | 1845 |

For each odd row, (a+d=2^{K+3-t}), and (t=v_2(A)).

## 6. What remains open

The root report's first 100,000 transitions show 49,717 level entries, cover every residue (2mod3^7), and have terminal residuals (D_{m exit}>4K+10) from (Kge4). This is substantial finite evidence but not an infinite invariant.

The next mathematical target is to prove, for every actual root level entry, both:
1. it is strictly above the fatal height (F_K) (so it does not halt at entry); and
2. if (D_{m in}=2^e r) with (r) odd, then (e=0) or (r>2K+5), so the level exits oddly.

The affine child-deficit formula and the fatal-hit equation reduce this to a root-specific arithmetic recurrence. The counterexample in the 100,000-transition report shows that a local condition on one level's odd residual does not automatically persist to the next level. No all-time proof, improved BB(6) bound, or exact (BB(6)) value is claimed.
