# Unimodular two-coordinate form of the #623 synchronization cocycle

**Status:** exact algebraic reduction; not yet an all-time synchronization proof.

This note refactors the existing `(A,B)) cocycle in
`SynchronizationResidueCocycle.md`. The change of coordinates is unimodular,
so it loses no information. Its benefit is that the four synchronization
forms become two primitive linear forms and two exact ternary rescalings.

## 1. Coordinates

Keep the signed S-window coordinates (X,Y), and define
[
U:=Y,\qquad V:=X+Y.
]
The map ((X,Y)mapsto(U,V)) has determinant (-1), hence is an invertible
integer change of coordinates. In the canonical root coordinates
(X=2g-gamma), (Y=6q), this is
[
U=6q,qquad V=2g-gamma+6q.
]

Recall
[
A=X-3Y,qquad B=3Y.
]
Then the four scalar forms in the exact synchronization criterion are
[
oxed{
A=V-4U,quad B=3U,quad
4A+5B=4V-U,quad 3A+4B=3V.
}
]
In particular, the four tests are not four unrelated residues: they are the
two forms (V-4U), (4V-U), together with (3U), (3V).

## 2. Exact residue criterion in the new coordinates

Put (M=3^n) and (N=3^{n-1}). The full-rectangle criterion from
`ExactSynchronizationCriterion.md` is equivalent to
[
4le [V-4U]_Mle M-3,
]
[
2le [4V-U]_Mle M-8,
]
[
1le [U]_Nle N-2,
]
[
1le [V]_Nle N-3.
]

The last two equivalences are exact, not estimates. For every integer (z),
[
[3z]_{3^n}=3[z]_{3^{n-1}},
]
because the representative on the right lies in ([0,3^n)). Thus
(2le[3U]_Mle M-5) is precisely
(1le[U]_Nle N-2), and
(2le[3V]_Mle M-7) is precisely
(1le[V]_Nle N-3).

This removes one ternary digit from each of the two scale tests. The remaining
full-depth exclusions are the two primitive forms (V-4U) and (4V-U).

## 3. Exact branch cocycle

Write the existing source/drain corrections as (kappa,phi), to avoid
confusing them with the four synchronization forms. The maintained updates are

Left:
[
X'=X-3Y+kappa,qquad Y'=3Y+phi.
]

Right:
[
X'=-4X-3Y+kappa,qquad Y'=3X+3Y+phi.
]

Substituting (U=Y), (V=X+Y) gives the simpler exact cocycle

**Left**
[
oxed{U'=3U+phi,qquad V'=V-U+kappa+phi.}
]

**Right**
[
oxed{U'=3V+phi,qquad V'=U-V+kappa+phi.}
]

The corresponding linear matrices are
[
L_{UV}=egin{pmatrix}3&0\-1&1end{pmatrix},
qquad
R_{UV}=egin{pmatrix}0&3\1&-1end{pmatrix},
]
with determinants (3) and (-3), respectively. These are conjugate to
the previously recorded ((A,B)) matrices by an integer unimodular
transformation; the determinant-(pm3) fact is unchanged.

The inverse recurrences are particularly useful:

- after a left step,
  [
  U=(U'-phi)/3,qquad V=V'+U-kappa-phi;
  ]
- after a right step,
  [
  V=(U'-phi)/3,qquad U=V'+V-kappa-phi.
  ]

So backward reconstruction divides exactly one of the two coordinates by
three at each step. On authentic root states (U=Y=6q) and (U'=Y'=6q');
therefore the exact correction satisfies (phi=Y'-3Yin6mathbb Z).
This gives a useful consistency check for any independently derived
source/drain correction table.

## 4. Why this is useful

The all-time problem can now be stated as avoidance, along the exact
two-coordinate cocycle, of the four residue bands
[
egin{aligned}
&[V-4U]_{3^n}
otin{0,1,2,3,3^n-2,3^n-1},\
&[4V-U]_{3^n}
otin{0,1,3^n-7,ldots,3^n-1},\
&[U]_{3^{n-1}}
otin{0,3^{n-1}-2,3^{n-1}-1},\
&[V]_{3^{n-1}}
otin{0,3^{n-2},3^{n-1}-1,3^{n-1}-2}.
end{aligned}
]
The first two sets are just the complements of the exact allowed intervals;
the last two are likewise boundary sets for the reduced-depth tests.

More importantly, the inverse recurrences expose a ternary digit at every
backward step. A prospective proof can therefore track the pair ((U,V))
as a two-register 3-adic process: the left branch shifts the (U)-register,
while the right branch shifts the (V)-register. The correction (phi)
supplies the low ternary digit, and (kappa+phi) supplies the affine
carry in the other register.

This is an exact reparameterization and an actionable reduction, **not** a
proof that the authentic orbit avoids the bands. The next mathematical task
is to express ((kappa,phi)) directly in the source's drain statistics and
prove a compatible carry invariant for the authentic S-window quotients.
The low-boundary carry warning in `WindowQuotientInterface.md` still applies:
global ((U,V)) alone cannot be substituted naively for every shifted
S-window quotient.
