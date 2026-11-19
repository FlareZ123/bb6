# F011 (#464): exact low-branch return map

**Status (19 November 2026): intermediate, not a machine decision.** The pinned accelerated map has an exact three-step low-branch return, an exact eight-family immediate-preimage classification for its two halt states, and the copied map admits the algebraic scalar potential below: every defined transition raises an integer rank by at least one. This proves acyclicity and linear escape for every infinite high-level orbit, but it does **not** exclude a finite hit of a halt state. The rank and eight-family Lean drafts are not yet verified against the original source: the rank draft currently fails its local Lean preflight, and the preimage draft has not been compiled. The BB(6) status is unchanged.

## Source and root

The machine is
\[
\texttt{1RB0RC\_1LC1RE\_1RA1LD\_0LC0LA\_1RF1RD\_---0RD}.
\]
The source-pinned upstream Lean module is [\`M_1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_HHH0RD.lean\`](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_HHH0RD.lean).

That module defines the accelerated state \(S(p,k,c)\), starts at \(S(0,2,0)\) after ten blank-tape steps, and proves
\[
\operatorname{IsHalt}(\text{target})
\iff
\operatorname{CollatzHalts}(\text{highLevelNext},\text{highLevelStart}).
\]
Write \(k=3q+r\), with \(r\in\{0,1,2\}\), and put \(d=c-q\). Its first high-level branch is
\[
c<q \quad\Longrightarrow\quad
S(p,3q+r,c)\mapsto S(p,3q+r-3c-2,4c+5).
\]

## Three-step return identity

While this branch continues to apply, the quotient and residue after one step are:

| Initial \(r\) | \(q'\) | \(r'\) | \(c'\) |
|---:|---:|---:|---:|
| 0 | \(q-c-1\) | 1 | \(4c+5\) |
| 1 | \(q-c-1\) | 2 | \(4c+5\) |
| 2 | \(q-c\) | 0 | \(4c+5\) |

Composing three such transitions gives, independently of the starting residue,
\[
\boxed{(q,r,c)\mapsto(q-21c-32,\ r,\ 64c+105).}
\]
The Boolean phase \(p\) is unchanged.

For clarity, the quotient subtractions over the three steps are:
- \(r=0\): \((c+1)+(4c+5+1)+(16c+25)=21c+32\);
- \(r=1\): \((c+1)+(4c+5)+(16c+25+1)=21c+32\);
- \(r=2\): \(c+(4c+5+1)+(16c+25+1)=21c+32\).

The corresponding \(c\)-values are \(c,\ 4c+5,\ 16c+25,\ 64c+105\).

## Closed form after complete blocks

Let \((q_n,r,c_n)\) be the state after \(n\) complete three-transition blocks, all of whose individual transitions satisfy the \(c<q\) guard. Then
\[
c_{n+1}=64c_n+105,\qquad
q_{n+1}=q_n-21c_n-32,\qquad r_n=r_0.
\]
Solving these recurrences gives
\[
\boxed{c_n=\frac{(3c_0+5)64^n-5}{3}},
\]
\[
\boxed{q_n=q_0-\frac{(3c_0+5)(64^n-1)}9+3n}.
\]
In particular, with \(\Delta_n=c_n-q_n\),
\[
\boxed{
\Delta_n=
\frac{(3c_0+5)(4\cdot64^n-1)-15-9q_0-27n}{9}.
}
\]

## Diagonal coordinate and the Mahler-type halt equation

The useful coordinate is
\[
u=3q+c.
\]
On a single \(c<q\) transition, \(c'=4c+5\), while
\[
u'=
\begin{cases}
u+2,&r=0,1,\\
u+5,&r=2.
\end{cases}
\]
Thus one complete three-transition block is diagonal in \((u,c)\):
\[
\boxed{(u,c,r)\mapsto(u+9,\ 64c+105,\ r).}
\]
Consequently
\[
u_n=u_0+9n,\qquad
c_n=\frac{(3c_0+5)64^n-5}{3}.
\]
Also
\[
d=c-q=\frac{4c-u}{3}.
\]
The two source-defined halting cases are
\[
(p,r,d)=(0,2,1)
\quad\text{or}\quad
(p,r,d)=(1,2,2).
\]
Set \(s=1\) when \(p=0\), and \(s=2\) when \(p=1\). Since \(p\) is unchanged during a \(c<q\) episode, a halt at its first \(r=2\) exit has the following exact form.

| Starting residue \(r_0\) | First possible \(r=2\) exit | First-exit inequalities | Necessary halt equation |
|---:|---|---|---|
| 0 | 2 transitions after \(n\) complete blocks | \(16c_n+18<u_n\le64c_n+96\) | \((3c_0+5)64^{n+1}=3u_0+27n+32+9s\) |
| 1 | 1 transition after \(n\) complete blocks | \(4c_n<u_n\le16c_n+18\) | \(16(3c_0+5)64^n=3u_0+27n+26+9s\) |
| 2 | At a complete-block boundary | \(u_n\le4c_n\) | \(4(3c_0+5)64^n=3u_0+27n+20+9s\) |

For each row, all earlier complete-block states must also satisfy \(u_j>4c_j\) for \(j<n\). The displayed inequalities enforce that the exit is at the indicated step, rather than an earlier state. The three equations combine into
\[
\boxed{
(3c_0+5)\,4^{\,3n+3-r_0}
=
3u_0+27n+32-6r_0+9s.
}
\]
This is the exact exponential-versus-linear residue equation behind the low-branch halting obstruction.

For a fixed episode start, there is at most one candidate \(n\): the difference between the left side and the \(27n\) term increases strictly, since
\[
(3c_0+5)4^{3(n+1)+3-r_0}-(3c_0+5)4^{3n+3-r_0}-27
=
63(3c_0+5)4^{3n+3-r_0}-27>0.
\]
Thus each \(c<q\) episode can be tested by an exact monotone search rather than by iterating every low-branch transition.

There is also an exact congruence filter for this episode equation. Put \(A=3c_0+5\), so \(\gcd(A,9)=1\). Reducing the halt equation modulo \(A\), using \(u_0=3q_0+c_0\) and \(3c_0\equiv-5\pmod A\), gives
\[
9n\equiv-3q_0-9+2r_0-3s\pmod A.
\]
Hence every possible halting block index belongs to the single residue class
\[
\boxed{n\equiv-9^{-1}(3q_0+9-2r_0+3s)\pmod{3c_0+5}.}
\]
Combining this arithmetic progression with the monotone crossing bound gives an exact finite candidate test for each episode; no assumption that \(n<A\) is needed. This is a necessary condition, not a root-wide exclusion.

## The generic outer branch is an affine 4/3 map

Put \(w=u-c=3q\). In each of the six generic \(c\ge q\) cases (the cases beyond the small exceptional values of \(d\)), the source map has the form
\[
k'=4q+\alpha,\qquad c'=d-\beta,
\]
where \(r'=(4q+\alpha)\bmod3\). The six parameter pairs are:

| Input phase and residue | Condition | \(\alpha\) | \(\beta\) |
|---|---:|---:|---:|
| \(p=0,r=0\) | \(d\ge1\) | \(-1\) | 0 |
| \(p=0,r=1\) | \(d\ge2\) | 3 | 1 |
| \(p=0,r=2\) | \(d\ge4\) | 8 | 4 |
| \(p=1,r=0\) | \(d\ge3\) | 7 | 2 |
| \(p=1,r=1\) | \(d\ge2\) | 6 | 1 |
| \(p=1,r=2\) | \(d\ge5\) | 12 | 5 |

Since \(u=4q+d\), these updates imply
\[
\boxed{u'=u+\alpha-\beta-r',\qquad
w'=\frac43w+\alpha-r'.}
\]
Thus, away from the finitely many boundary subcases, the outer map advances \(u\) by a bounded integer and applies an affine \(4/3\) expansion to \(w=3q\), while resetting \(c\) to the previous gap minus a small constant. This identifies the precise source of the \(4/3\) cascade in the high-level dynamics. The exceptional \(d\)-values and \(q=0\) branches remain part of the exact map and must not be dropped in a proof.

There is also a uniform bound on any consecutive run of these generic outer steps. Since the table has \(\beta\ge0\) and \(\alpha-r'\ge-3\),
\[
q'=\frac{4q+\alpha-r'}3\ge\frac{4q-3}{3},\qquad
d'=d-\beta-q'\le d-q'.
\]
If \(q\ge4\), then \(q'\ge q+1\) and \(q'-3\ge\frac43(q-3)\). Therefore, if \(L\) consecutive generic outer steps all remain in \(d\ge0\), starting from \((q_0,d_0)\) with \(q_0\ge4\), then
\[
d_0\ge\sum_{j=1}^{L}q_j
\ge 3L+4(q_0-3)\left(\left(\frac43\right)^L-1\right).
\]
In particular,
\[
L\le
\log_{4/3}\left(1+\frac{d_0}{4(q_0-3)}\right).
\]
This bounds generic stretches of the outer bridge. It does not by itself bound the full bridge, because the exceptional small-\(d\) branches can intervene and must be handled separately.

Writing \(\epsilon=\alpha-r'\) and \(\delta=\alpha-\beta-r'\), each such generic outer step is
\[
w'=\frac43w+\epsilon,\qquad u'=u+\delta.
\]
Along a bridge of \(L\) generic outer steps, with branch-dependent digits \((\epsilon_j,\delta_j)\),
\[
u_L=u_0+\sum_{j=0}^{L-1}\delta_j,
\]
\[
3^Lw_L=4^Lw_0+
\sum_{j=0}^{L-1}4^{L-1-j}3^{j+1}\epsilon_j.
\]
The digits come from the six branch types above and depend on the evolving state; they are not an independent or random sequence. This formula isolates the unresolved outer dynamics as a constrained rational-base \(4/3\) digit process, which is the part that must be controlled to settle the halt-preimage avoidance problem.

## Exact one-step preimage set of the halt states

Let
\[
H_0(Q)=S(0,3Q+2,Q+1),\qquad
H_1(Q)=S(1,3Q+2,Q+2).
\]
These are the two source-defined halt states: phase-false with \((r,d)=(2,1)\), and phase-true with \((r,d)=(2,2)\). Inverting the pinned highLevelNext definition gives **eight** immediate-predecessor families. Here \(d=c-q\).

| Predecessor \((p,r,q,d)\) | Parameter range | Image |
|---|---:|---|
| \((0,1,5m+5,-4m-5)\) | \(m\ge0\) | \(H_0(4m+4)\) |
| \((1,1,5m+4,-4m-4)\) | \(m\ge0\) | \(H_1(4m+3)\) |
| \((0,0,3m,4m+1)\) | \(m\ge1\) | \(H_1(4m-1)\) |
| \((0,1,3m+2,4m+5)\) | \(m\ge0\) | \(H_0(4m+3)\) |
| \((0,2,3m,4m+7)\) | \(m\ge0\) | \(H_0(4m+2)\) |
| \((1,0,3m+1,4m+7)\) | \(m\ge0\) | \(H_1(4m+3)\) |
| \((1,1,3m+2,4m+6)\) | \(m\ge0\) | \(H_0(4m+4)\) |
| \((1,2,3m+2,4m+12)\) | \(m\ge0\) | \(H_0(4m+6)\) |

The first two rows are the \(c<q\) preimages. In that branch, \(r=0,1,2\) maps respectively to residues \(1,2,0\); hence only input residue \(r=1\) can map directly to a halt state. Its update is \(q'=-d-1\), \(d'=4q+5d+6\). Solving \(d'=1\) for phase \(p=0\), or \(d'=2\) for phase \(p=1\), gives exactly the first two families.

The remaining six rows are the \(c\ge q\) cases. For each of the six input pairs \((p,r)\), require the output residue to be \(2\), then impose the output gap \(d'=1\) or \(2\) according to the output phase. The resulting congruence and linear equations give the six displayed families. In particular, the \((p,r)=(0,2)\) generic branch uses \(k'=4q+8\), \(c'=d-4\); the \((p,r)=(1,2)\) generic branch uses \(k'=4q+12\), \(c'=d-5\).

### Correction to the earlier nine-family table

An earlier version included the extra row \((p,r,q,d)=(0,2,0,3)\mapsto H_0(2)\). That row is false. The pinned source at lines 1217–1221 says that the \(p=0,r=2,d=3\) branch maps
\[
S(0,3q+2,q+3)\longmapsto S(0,4q+6,3).
\]
For \(q=0\), this is \(S(0,6,3)\), whose quotient/remainder are \((2,0)\), not the required residue \(2\). More generally, the output residue is \(2\) only when \(q=3m+2\); then its quotient is \(4m+4\) and its gap is \(3-(4m+4)=-4m-1<0\). Thus no state in this entire \(d=3\) branch is an immediate predecessor of either halt family.

The standalone HaltPreimageAudit.lean file has been locally compiled against a literal transcription of the pinned highLevelNext definition; its three declarations report only propext, with no sorryAx or native_decide. This is a copied-definition audit, not an import-based source-chain certificate. HaltPreimageFamilies.lean drafts the eight-family inversion but has not been locally preflighted. HaltPreimageRank.lean drafts the lexicographic pair rank and two-step growth theorem, but its current Lean 4.36.0-rc2 preflight fails because split_ifs is unavailable in the Lean-core environment; its downstream axiom reports include sorryAx. Replacing split_ifs by core split also failed. Consequently no rank or preimage theorem is presently Lean-verified, and no CI was dispatched: the repository's current acceptance gate requires a successful exact local preflight first.

## Scalarization of the monotone potential

The branch arithmetic gives a simpler integer rank than the lexicographic pair in HaltPreimageRank.lean. Write \(q=\lfloor k/3\rfloor\), \(r=k\bmod 3\), and \(d=c-q\). Define
\[
\lambda(p,k)=
\begin{cases}
0,&p=0,\\
2,&p=1,\ k=0,\\
3,&p=1,\ k>0,
\end{cases}
\qquad
W(p,k,c)=3q+c+\lambda(p,k),
\]
and let \(\tau(k)=\mathbf 1_{r=2}\). The scalar rank is
\[
\boxed{R(p,k,c)=2W(p,k,c)+\tau(k).}
\]

On the low branch \(c<q\), direct substitution gives
\[
W'-W=
\begin{cases}
2,&r=0,\\
2,&r=1,\\
5,&r=2.
\end{cases}
\]
For the outer branch \(c\ge q\), the following table gives the exact increment \(\Delta W=W'-W\). In each triple, entries correspond to \(q\equiv0,1,2\pmod3\), respectively. The exceptional \(q=0\) rows are separated because the source map has special branches.

**Phase \(p=0\):**

| Input residue \(r\) | Condition | \(q\equiv0\) | \(q\equiv1\) | \(q\equiv2\) |
|---:|---|---:|---:|---:|
| 0 | \(q=0,d=0\) | 3 | — | — |
| 0 | \(q=0,d\ge1\) | 2 | — | — |
| 0 | \(q\ge1,d=0\) | 4 | 7 | 6 |
| 0 | \(q\ge1,d\ge1\) | 0 | 2 | 1 |
| 1 | \(d=0\) | 3 | 3 | 3 |
| 1 | \(d=1\) | 3 | 2 | 4 |
| 1 | \(d\ge2\) | 2 | 1 | 0 |
| 2 | \(d=0\) | 5 | 5 | 5 |
| 2 | \(d=1\) | halt | halt | halt |
| 2 | \(d=2\) | 4 | 3 | 2 |
| 2 | \(d=3\) | 6 | 5 | 4 |
| 2 | \(d\ge4\) | 2 | 4 | 3 |

**Phase \(p=1\):**

| Input residue \(r\) | Condition | \(q\equiv0\) | \(q\equiv1\) | \(q\equiv2\) |
|---:|---|---:|---:|---:|
| 0 | \(q=0\), any \(d\) | 0 | — | — |
| 0 | \(q\ge1,d=0\) | \(4q+2\) | \(4q+1\) | \(4q\) |
| 0 | \(q\ge1,d=1\) | 5 | 5 | 5 |
| 0 | \(q\ge1,d=2\) | 5 | 7 | 6 |
| 0 | \(q\ge1,d\ge3\) | 4 | 3 | 5 |
| 1 | \(d=0\) | 4 | 4 | 4 |
| 1 | \(d=1\) | 3 | 2 | 4 |
| 1 | \(d\ge2\) | 2 | 1 | 0 |
| 2 | \(d=0\) | 4 | 4 | 4 |
| 2 | \(d=1\) | 5 | 5 | 5 |
| 2 | \(d=2\) | halt | halt | halt |
| 2 | \(d=3\) | 3 | 2 | 4 |
| 2 | \(d=4\) | 5 | 4 | 6 |
| 2 | \(d\ge5\) | 4 | 3 | 2 |

Thus \(\Delta W\ge0\) on every defined transition. Its only zero cases are:
1. \(p=0,r=0,q=3m\) with \(m\ge1\) and \(d\ge1\);
2. \(p=0,r=1,q=3m+2\) with \(m\ge0\) and \(d\ge2\);
3. \(p=1,r=0,q=0\), with arbitrary \(d\ge0\);
4. \(p=1,r=1,q=3m+2\) with \(m\ge0\) and \(d\ge2\).

In all four zero-increment cases the output has residue \(r'=2\), whereas the input has \(r\ne2\). Therefore
\[
R'-R=2(W'-W)+\tau'-\tau\ge1
\]
for every defined transition: if \(W'-W\ge1\), the worst possible tie-break change is \(-1\); if \(W'-W=0\), the tie-break increases by one. This is a complete algebraic case proof for the literal copied map; it still needs a Lean proof and an import-based transfer to the pinned upstream definition.

For any defined orbit prefix \(s_0\to s_1\to\cdots\to s_n\), it follows that
\[
R(s_n)\ge R(s_0)+n.
\]
The blank-start high-level state is \(s_0=S(0,2,0)\), with \(R(s_0)=1\), so
\[
\boxed{W(s_n)\ge\lceil n/2\rceil.}
\]
Consequences: no positive-length cycle exists in the high-level map, and every infinite orbit escapes every bounded-\(W\) region. More quantitatively, a path from the root to \(H_0(Q)\) has at most \(8Q+2\) transitions, and a path to \(H_1(Q)\) has at most \(8Q+10\) transitions. These bounds are parameter-dependent; they do not bound \(Q\), and they do not prove that the root avoids all eight predecessor families. The unresolved problem remains an all-parameter root-to-halt-preimage exclusion.

This is an exact backward reduction: the root orbit can halt only if it visits one of these eight affine predecessor families. It does not prove that the orbit avoids them; the remaining task is a forward-invariant or backward-reachability argument for the root \(S(0,2,0)\).


## What this reduces, and what remains open

The repeated \(c<q\) transition is now explicit and diagonalized: \(u\) advances linearly by 9 per three-step block, while \(c\) follows an affine base-64 recurrence. A possible halt at the first \(r=2\) exit is reduced to one monotone exponential-linear equation with first-exit inequalities.

The unresolved root problem is to characterize the episode-start parameters \((p,q_0,r_0,c_0)\) generated by the other high-level branches, then determine whether any of these equations can hold. Halts reached directly from a state in the \(c\ge q\) branches also require their own analysis; the equations above classify only first \(r=2\) exits from a \(c<q\) episode.

The source theorem transfers a proof that the high-level orbit avoids both halting cases into a nonhalting proof for the original blank-tape machine. Conversely, finding one valid equation with its first-exit inequalities would identify a halting orbit segment.

No finite simulation is used as evidence for either outcome here. No conclusion about F011's halting status is claimed.


## 2026-11-19 exact-transcription local Lean check

The standalone `HaltPreimageAudit.lean` has now been recompiled locally with Lean 4.36.0-rc2 against the exact pinned `highLevelNext` transcription. The three declarations concerning the `p=false, r=2, d=3` branch compile, with `#print axioms` reporting `[propext]` for each and no `sorryAx`.

This validates the isolated copied-definition branch audit only. It is not an import-based proof of the upstream source chain, and it does not certify the complete eight-family preimage characterization or the root orbit. `HaltPreimageFamilies.lean` and `HaltPreimageRank.lean` remain uncompiled drafts: replacing Mathlib's `split_ifs` with core `split` has not yet discharged the resulting branch obligations. Earlier rank experiments must be rerun against the corrected exact transcription; an initial scratch copy had incorrect `p=true, r=0` outputs.

A bounded Python comparison of the eight-family predicate against the copied transition map over all `p∈{false,true}`, `k,c<1000` (2,000,000 states) found no discrepancy. This is finite computational evidence, not a universal proof. No BB(6) or F011 halting-status conclusion follows.
