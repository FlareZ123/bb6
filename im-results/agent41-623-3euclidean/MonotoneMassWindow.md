# Monotone mass indexing for the #623 moving 3-adic window

**Status:** exact algebraic window-shift lemma derived from the existing four-sector cocycle and source-verified depth/mass bounds. It does not establish the missing middle-digit language closure or prove #623 nonhalting.

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

## 3. Consequence for the moving ternary window

Use the same unified correction/terminal envelope as the carry-transducer dossier:
[
B(ell)=max(34ell+140, 36ell+88).
]
The first term bounds the affine carry corrections; the second bounds the centered terminal residual. Since (ell_{S'}-ell_Sin{0,1}),
[
Ble B'le B+36<3B
]
(the uniform lower bound is (Bge140)).

Define (k,j) to be the least integers with
[
3^k>B,qquad 3^j>B^3.
]
For the next state define (k',j') from (B'). Then
[
oxed{k'-kin{0,1},qquad j'-jin{0,1,2,3}.}
]
The lower bounds follow from (B'ge B). For the upper bounds,
(3^{k+1}>3B>B') and
(3^{j+3}=27cdot3^j>27B^3>B'^3).

Thus the moving window advances only forward, by at most one low digit and three high digits per root transition. Since (kge5) and (jge3k-2), its interior remains nonempty.

In the transducer notation, the next state's required middle interval is
([k'+2,j'-2)). It contains the old output subinterval
[
[k+3,j-2),
]
because (k'+2le k+3) and (j'-2ge j-2). Therefore **one low-end buffer digit is sufficient for window overlap; no high-end trimming is needed**. The current transducer can simply be run three positions farther at the high end to supply the next window.

This is a useful reduction of the moving-boundary problem to a finite set of shifts. It does not prove that the output is nonmonochromatic on ([k+3,j-2)), so it does not by itself close the carry-language induction.

## 4. Proof status and next obligation

The derivation uses the exact four-sector ((p,q)) cocycle, the source depth package in `RootRayDrainDepthSource.lean`, and the source mass-growth theorem `next_strict_mass`. The individual source modules already exist in the manual pinned-source workflow. The combined mass-indexed window-shift consumer has not yet been added to that workflow or kernel-checked as a single theorem.

The finite reset-word and two-digit-buffer observations in `SynchronizingWordScan.md` remain computational. In particular, a reset subword somewhere in a current window does not imply another reset in the output suffix: the existing diagnostic records a constant suffix at root index 33. The remaining mathematical task is an invariant on the authentic output language or its boundary state, not another finite scan.

Related interfaces:
- `RootRayGapCocycle.md` — exact ((D,R)) corrections and gap/scale recurrence.
- `../agent8-623-inverse/RootRayDrainDepthSource.lean` — source-imported signed-drop and drain-depth bounds.
- `../agent49-parity623/Parity623Source.lean` — source mass-growth theorem `next_strict_mass`.
- `../agent41-623-integer-carry-transducer/README.md` — finite carry transducer and existing diagnostics.
