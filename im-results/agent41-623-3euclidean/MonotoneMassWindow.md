# Monotone mass indexing for the #623 moving 3-adic window

**Status:** exact algebraic window-shift lemma derived from the four-sector cocycle and source-verified depth/mass bounds. The corrected shared buffer is now \(B(\ell)=34\ell+122\), giving both low- and high-end shifts in \(\{0,1\}\). This does not establish the missing middle-digit language closure or prove #623 nonhalting.

## 1. Exact mass increment

Write a canonical root-section state as (D(a,d)), and put
[
S=a+d,qquad q=min(a,d),qquad p=|a-d|,qquad g=p-3q.
]
The two-statistic cocycle uses the signed first-counter drop (D_0) and the full drain iteration count (R) (the right-even initial evaluator is included in (R)). To avoid confusing the state (D(a,d)) with the signed drop, write the latter as (c) in the formulas below.

The exact correction table from `RootRayGapCocycle.md` gives
[
eta:=eta+delta=
egin{cases}
c+2R+9&mathrm{LO},\
c+2R+6&mathrm{LE},\
c+2R+4&mathrm{RO},\
c+2R+4&mathrm{RE}.
end{cases}
]
The exact gap/scale updates imply, in either output orientation,
[
oxed{S'=S+q+eta.}
]
Indeed, for left output (p'=g-delta+eta), (q'=3q+delta); for right output (p'=-g+delta-eta), (q'=p+eta). In both cases
[
p'+2q'=g+6q+eta+delta=p+3q+eta=S+q+eta.
]
No sign-of-(g) approximation is used.

## 2. Replace the smaller-counter depth by a mass depth

Let
[
	au(n)=rac{3^n-1}{2},qquad
ell_S=min{n:S+3le	au(n)}.
]
The canonical drain block in every sector is at most (q+3), and (qle S). Thus the source depth package can be instantiated with (n=ell_S). Its bounds give
[
cleell_S+1,qquad Rleell_S.
]
Consequently, uniformly over all four sectors,
[
etale3ell_S+10.
]

For (Sge20),
[
ell_Slelfloor S/2floor-1le S/2-1.
]
To see this, put (n=lfloor S/2floor-1ge9). Then (Sle2n+3), while (3^nge4n+13) for (nge9) (base case (n=9), followed by immediate induction). Hence
[
	au(n)ge2n+6ge S+3,
]
so (ell_Sle n).

It follows that every successful canonical transition with (Sge20) satisfies
[
S'=S+q+eta
le S+rac S2+3left(rac S2-1ight)+10
=oxed{3S+7}.
]
The source theorem `next_strict_mass` gives (S'ge S+7). Therefore (S'>S), and
[
	au(ell_S+1)=3	au(ell_S)+1
ge3(S+3)+1=3S+10
ge S'+3.
]
Monotonicity of (	au) now yields the exact depth-shift bound
[
oxed{ell_{S'}-ell_Sin{0,1}.}
]
The threshold (Sge20) is automatic after two successful returns from the blank start (D(0,7)), since the source mass theorem gives at least (+7) per return.

## 3. Correction-only buffer and one-digit moving-window shifts

The earlier envelope
\[
B(\ell)=\max(34\ell+140,36\ell+88)
\]
is unnecessarily wide. Use the full-drain statistics from "DrainDigitTransducerCarry.lean": \(E=n_2\), \(R=n_1+n_2\), and
\(D=L-2E\). The source theorem "runStats_weight_bounds" gives
\(0\le E\le R\le L\), while
"SignedCoordinateNormalForm.correction_buffer_closed" gives
\[
|C|\le34L+122,\qquad |F|\le34L+122.
\]
Since \(L\le\ell_S\), both affine corrections are bounded by
\[
\boxed{B(\ell_S)=34\ell_S+122.}
\]

This same buffer also dominates the exact terminal residual. The four
"TerminalRatio4" bounds give
\[
|x'|\le\max(12n+88,12n+62,12n+38,18n+50)
       =18n+50\le18\ell_S+50
       <34\ell_S+122.
\]
Thus the correction-only buffer suffices both for the carry calculation
and for the terminal-strip contradiction; the old \(36\ell+88\) term
was only a loose terminal envelope.

From Section 2, \(\ell_{S'}-\ell_S\in\{0,1\}\). Hence
\[
B\le B'\le B+34.
\]
For \(S\ge20\), \(\ell_S\ge4\), because
\(\tau(3)=13<S+3\). Therefore \(B\ge34\cdot4+122=258\).
In particular \(5(B+34)\le7B\), so
\[
(B')^3\le(B+34)^3
\le\left(\frac75\right)^3B^3
=\frac{343}{125}B^3
<3B^3.
\]
Also \(B'\le B+34<3B\).

Let \(k,j\) be least with \(3^k>B\) and \(3^j>B^3\), and
define \(k',j'\) from \(B'\). Monotonicity gives the lower bounds.
For the upper bounds,
\[
3^{k+1}=3\cdot3^k>3B>B',
\qquad
3^{j+1}=3\cdot3^j>3B^3>(B')^3.
\]
Consequently the corrected source shift bound is
\[
\boxed{k'-k\in\{0,1\},\qquad j'-j\in\{0,1\}.}
\]
This improves the previous high-end bound \(j'-j\in\{0,1,2,3\}\):
the next window needs at most one new high digit, not three.

The next required interval \([k'+2,j'-2)\) still contains the old
output subinterval \([k+3,j-2)\), since \(k'\le k+1\) and \(j'\ge j\).
The corrected finite diagnostic reports only shifts \((0,0),(0,1),(1,1)\);
the source bound also permits \((1,0)\), which remains a possible
transition until excluded by a stronger invariant.

This is an algebraic improvement to the moving-boundary interface. It
does not prove that the output is nonmonochromatic on the overlap interval
or that the reset DFA accepts every future authentic root window.

## 4. Proof status and next obligation

The derivation uses the exact four-sector ((p,q)) cocycle, the source depth package in `RootRayDrainDepthSource.lean`, and the source mass-growth theorem `next_strict_mass`. The individual source modules already exist in the manual pinned-source workflow. The combined mass-indexed window-shift consumer has not yet been added to that workflow or kernel-checked as a single theorem.

The finite reset-word and two-digit-buffer observations in `SynchronizingWordScan.md` remain computational. In particular, a reset subword somewhere in a current window does not imply another reset in the output suffix: the existing diagnostic records a constant suffix at root index 33. The remaining mathematical task is an invariant on the authentic output language or its boundary state, not another finite scan.

Related interfaces:
- `RootRayGapCocycle.md` — exact ((D,R)) corrections and gap/scale recurrence.
- `../agent8-623-inverse/RootRayDrainDepthSource.lean` — source-imported signed-drop and drain-depth bounds.
- `../agent49-parity623/Parity623Source.lean` — source mass-growth theorem `next_strict_mass`.
- `../agent41-623-integer-carry-transducer/README.md` — finite carry transducer and existing diagnostics.
