# F011 (#464): exact low-branch return map

**Status:** intermediate mathematical result. This is an exact reduction of one branch of the accelerated orbit, not a proof that the machine halts or does not halt.

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

The standalone HaltPreimageAudit.lean file locally checks this whole \(p=0,r=2,d=3\) branch against a literal transcription of the pinned highLevelNext definition using Lean 4.36.0-rc2. Its three declarations have axiom reports containing only propext; there is no sorryAx or native_decide. This is a copied-definition audit, not an import-based source-chain certificate. The eight-family inversion above is now drafted as `F011.highLevelNext_halt_preimage_iff` in `HaltPreimageFamilies.lean`, with `F011.highLevelNext_none_iff` tying the two target forms to `none`. This new file is over the literal transcription, has not been compiled in this invocation, and is not yet an import-based source-chain certificate. Treat it as unverified until a Lean 4.36.0-rc2 compile and source-import comparison pass.

This is an exact backward reduction: the root orbit can halt only if it visits one of these eight affine predecessor families. It does not prove that the orbit avoids them; the remaining task is a forward-invariant or backward-reachability argument for the root \(S(0,2,0)\).


## What this reduces, and what remains open

The repeated \(c<q\) transition is now explicit and diagonalized: \(u\) advances linearly by 9 per three-step block, while \(c\) follows an affine base-64 recurrence. A possible halt at the first \(r=2\) exit is reduced to one monotone exponential-linear equation with first-exit inequalities.

The unresolved root problem is to characterize the episode-start parameters \((p,q_0,r_0,c_0)\) generated by the other high-level branches, then determine whether any of these equations can hold. Halts reached directly from a state in the \(c\ge q\) branches also require their own analysis; the equations above classify only first \(r=2\) exits from a \(c<q\) episode.

The source theorem transfers a proof that the high-level orbit avoids both halting cases into a nonhalting proof for the original blank-tape machine. Conversely, finding one valid equation with its first-exit inequalities would identify a halting orbit segment.

No finite simulation is used as evidence for either outcome here. No conclusion about F011's halting status is claimed.
