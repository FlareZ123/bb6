# Structural reduction of the TM63 `Rsts1_v2` source obligation

**Status: proof-interface derivation, not a machine theorem.** This note extracts the exact induction used by the pinned Rocq source and states the original-TM2 counted interface that would make the entire `Rsts1_v2` itinerary a routine composition. It is kept in `im-results/` because the one-step source theorems are not yet universal or fully compiled.

## 1. Exact Rocq structure

At pinned source revision `ccz181078/busycoq` `3f302b87f5fb933c46e97672ffbb6907f373fb6`, `verify/SOBCv5.v` defines:

- `Rst2`: `S1(L,a0+1,m2,a,0,b) -->* S1(L,a0,m1,a+b+2,0,2^b-1)`.
- `Rst1`: `S1(L,a0+1,m1,a,0,b) -->* S1(L,a0,m0,a+b+2,0,2^b-1)`.
- `Rst0`: `S1(L,a0+1,m0,a,0,b) -->* S1(L,a0,m2,a+b+1,0,2^b-1)`.

The arithmetic recurrences are
[
t_2(0,b)=b,qquad t_2(j+1,b)=2^{t_2(j,b)}-1,
]
[
st_2(0,b)=b,qquad st_2(j+1,b)=st_2(j,b)+t_2(j+1,b).
]
Thus (st_2(j,b)=sum_{i=0}^{j}t_2(i,b)).

The Rocq lemma `Rsts` is an induction on (q), with exactly three source transitions per induction step:
[
S1(L,3q+a_0,m_2,b,0,2^b-1)
longrightarrow^*
S1(L,a_0,m_2,st_2(3q,b)+5q,0,t_2(3q+1,b)).
]
Its successor case first applies the induction hypothesis at (a_0+3), then `Rst2`, `Rst1`, and `Rst0`. The right-counter values consumed by those three steps are (t_2(3q+1,b)), (t_2(3q+2,b)), and (t_2(3q+3,b)). Their unary increments are respectively (+2,+2,+1), giving the (+5) per cycle and the (st_2) sum.

The Rocq `Rsts1` is then only `Rsts` with residual index 1 followed by one `Rst2`:
[
S1(L,3q+1,m_2,b,0,2^b-1)
longrightarrow^*
S1(L,0,m_1,st_2(3q+1,b)+5q+2,0,t_2(3q+2,b)).
]
Likewise `Rsts2` follows from `Rsts` with residual index 2 and then `Rst2`, `Rst1`:
[
S1(L,3q+2,m_2,b,0,2^b-1)
longrightarrow^*
S1(L,0,m_0,st_2(3q+2,b)+5q+4,0,t_2(3q+3,b)).
]
Finally, `Rsts1_v2` is just the arithmetic rewrite (n=3q+1) from (nmod3=1), followed by `Rsts1`. There is no additional machine simulation hidden in that final lemma.

## 2. Counted original-TM2 interface

The repository's source rows use the original infinite-tape `BB6Coverage.run` semantics. A suitable full one-step theorem family is:

[
egin{aligned}
Rst2_{m TM2}:&quad
run tm2 C_2(L,n,a,b) (S1(L,n+1,2,a,0,b,h))\
&=some(S1(L,n,1,a+b+2,0,2^b-1,h+5+3b)),\
Rst1_{m TM2}:&quad
run tm2 C_1(L,n,a,b) (S1(L,n+1,1,a,0,b,h))\
&=some(S1(L,n,0,a+b+2,0,2^b-1,h+5+3b)),\
Rst0_{m TM2}:&quad
run tm2 C_0(L,n,a,b) (S1(L,n+1,0,a,0,b,h))\
&=some(S1(L,n,2,a+b+1,0,2^b-1,h+5+3b)).
end{aligned}
]
Here (C_m) must be the exact primitive successful-move count (the current candidate is `proposedIncrementCost m (n+1) a b)); the displayed endpoint/head shift follows the current q4-prefix plus counted-drain interfaces. These statements need full tape equality, not only finite-window agreement, and each exported theorem needs a transitive `sorryAx`-free axiom audit.

If these three theorems are available for every admissible (L,n,a,b), then `Rsts` can be ported by the same induction as Rocq, composing the three runs and adding their counts. The huge tower values never need to be evaluated: `t2` and `st2` remain symbolic natural-number recurrences.

## 3. Derived head displacement and cost recurrence

The one-step row interface advances the head by (5+3b_{m in}). In `Rsts`, the successive input right-counter lengths are
(t_2(1,b),t_2(2,b),ldots,t_2(3q,b)). Therefore the total head displacement is
[
H_{m Rsts}(q,b)=15q+3sum_{i=1}^{3q}t_2(i,b)
=15q+3(st_2(3q,b)-b).
]
This follows by summing the one-step head shifts; it is an arithmetic identity, not yet a Lean theorem.

The exact primitive-move count can be defined without expanding the tower by a recurrence that mirrors the proof:
[
C_{m Rsts}(0,L,a_0,b)=0,
]
[
C_{m Rsts}(q+1,L,a_0,b)=
C_{m Rsts}(q,L,a_0+3,b)+
C_2(L,a_0+3,A_0,B_0)+
C_1(L,a_0+2,A_1,B_1)+
C_0(L,a_0+1,A_2,B_2),
]
where the (A_i,B_i) are the intermediate parameters obtained by the three displayed one-step endpoints. This is preferable to expanding an astronomical closed numeral. The Lean proof should establish the run equality and cost recurrence together by induction.

For `Rsts1`, append one `Rst2` at residual index 1. Its head displacement is
[
H_{m Rsts1}(q,b)=15q+5+3(st_2(3q+1,b)-b).
]
For `Rsts2`, append `Rst2` and `Rst1` at residual indices 2 and 1. These are straightforward two-step compositions once the generic one-step interfaces are established.

## 4. Research consequence

The hard open obligation is **not** the division-modulo-3 wrapper `Rsts1_v2`. It is the universal original-source realization of the three one-step `Rst2/Rst1/Rst0` macros, including exact primitive counts and complete infinite-tape preservation. The present repository contains several residue-specific q4 prefixes and counted drains; they are useful cases, but they do not yet supply the three universal interfaces.

This suggests a disciplined route:

1. Complete and validate the current Rst1Prime/Bridge8 source gate, which is a prerequisite for the authentic root path.
2. Establish the one-step reset theorem families for all admissible indices (or a genuinely general q4 prefix lemma that subsumes the residue cases).
3. Prove the `Rsts` induction once, using the recurrence above.
4. Derive `Rsts1`/`Rsts2` and then `Rsts1_v2`/`Rsts2H` without further machine-specific rediscovery.
5. Compose the counted Rst1' applications and terminal query only after all source/axiom gates pass.

The current M0 residue-seven and M2 residue-six root rows are individual points/families on this route, not a proof of the universal one-step interface. The second Rst1' stage and the final halting theorem remain open.
