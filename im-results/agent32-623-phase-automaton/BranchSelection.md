# Conditional branch-selection reduction for the #623 root cocycle

**Status:** the conditional algebraic lemma is now machine-checked in `BranchSelection.lean`. It remains a standalone, non-source-imported conditional result, not an all-time root invariant, and it does not decide machine #623. Keep in `im-results/`.

## Definitions

Write (q=min(a,d)), (p=|a-d|), (g=p-3q). In the four canonical sectors, the old-ray distance is

[
h=
egin{cases}
g-9 & mathrm{LO},\
g-5 & mathrm{LE},\
(g-1)/2 & mathrm{RO},\
(g-2)/2 & mathrm{RE}.
end{cases}
]

Use the full-drain convention from `RootRayGapCocycle.md`: (D) is the signed first-counter drop, (R) counts every evaluator call including the initial right-even evaluator, and the exact output-side threshold is

[
T=3D+2R+c_T,qquad
c_T=(19,10,-4,2)
]

in LO/LE/RO/RE respectively. The source cocycle says the next output is left-oriented iff (gge T), and right-oriented iff (g<T).

Let (ell) be least with (	au(ell)=(3^ell-1)/2ge q+3). The depth bounds used in the root-cocycle dossier are

[
|D|le ell+1,qquad 0le Rleell.
]

The source terminal-window estimates for (nge10), together with (nleellle n+1), are all dominated by the common window

[
W=9ell+22.
]

## Lemma

Assume (ellge3), the depth bounds above, and (|h|>W). Then

[
oxed{	ext{output is left-oriented}iff g>0.}
]

Equivalently, the exact threshold test (gge T) reduces to the sign test (g>0) whenever the current state is outside the common terminal window.

### Proof

The four sector definitions give the uniform lower bound

[
|g|>9ell+13.
]

Indeed:
- LO: (|g|=|h+9|ge |h|-9>9ell+13);
- LE: (|g|=|h+5|ge |h|-5>9ell+17);
- RO: (|g|=|2h+1|ge2|h|-1>18ell+43);
- RE: (|g|=|2h+2|ge2|h|-2>18ell+42).

On the other hand,

[
|T|
le 3|D|+2R+|c_T|
le 3(ell+1)+2ell+19
=5ell+22.
]

For (ellge3), (9ell+13>5ell+22). Hence (|g|>|T|), so (g-T) has the same strict sign as (g). The exact output-side criterion therefore becomes the claimed sign test. (square)

## Lean check

'BranchSelection.lean' formalizes the four sector relations, exact threshold
offsets, and the conditional sign reduction. It proves:

- 'g_far_of_h_far': the four sector definitions and the outside-window
  hypothesis imply \(|g|>9\ell+13\);
- 'threshold_bounds': the depth package implies \(|T|\le5\ell+22\);
- 'output_left_iff_positive_g' and 'output_right_iff_negative_g': under
  those hypotheses, the exact test \(g\ge T\) is equivalent to \(g>0\),
  and its complementary branch to \(g<0\).

The file compiles with Lean 4.36.0-rc2 and warnings treated as errors.
The principal theorem axiom profiles are exactly
'[propext, Quot.sound]'. The offset bound is proved by computation.

**Boundary:** the hypotheses \(\ell\ge3\), \(|h|>9\ell+22\),
\(|D|\le\ell+1\), and \(0\le R\le\ell\) are assumptions in this
module. It does not source-import the cocycle/depth wrapper or prove these
conditions along the authentic root orbit. Thus the branch-choice
simplification is formalized conditionally, but the phase invariant and
#623 nonhalting claim remain open.

## Research consequence

This removes the drain-statistic comparison from the *branch-choice* part of a proposed phase automaton, conditional on maintaining the nonterminal-window invariant. The root's orientation transition is then the sign branch of the perturbed 3-Euclidean map. The drain transducer is still needed for the exact affine correction digits and the carry phase.

The implication is deliberately conditional: it does not prove (|h|>W) for the authentic root. The finite middle-block/synchronization argument must still establish that invariant from a source-checked prefix and preserve it under the exact digit-pair transducer. The depth wrapper ((|D|,R)) should also be source-imported and axiom-audited before this note is treated as a fully formalized lemma.

## Interfaces

- `im-results/agent1-machine623-3euclidean-correction-bounds/RootRayGapCocycle.md`: exact threshold, (D,R) identities, and sector terminal windows.
- `im-results/agent1-machine623-3euclidean-correction-bounds/SignedCoordinateNormalForm.md`: full-drain convention and finite carry rectangles.
- `im-results/agent41-623-3euclidean/MonotoneMassWindow.md`: moving-window shifts (k'-kin{0,1}), (j'-jin{0,1,2,3}).
- `im-results/agent1-machine623-3euclidean-correction-bounds/SynchronizingWordScan.md`: finite synchronization diagnostics; no all-time closure theorem yet.


## Sharper form directly from the central digit block

The synchronization proof is intended to establish nonmonochromaticity of the central (x)-digit block itself. This gives a stronger and more direct hypothesis than (|h|>W).

Set
[
B(ell)=max(34ell+122,36ell+88).
]
The middle-block certificate says that if the digits of (xmod 3^j) in the central interval are neither all 0 nor all 2, then
[
min(r,3^j-r)>B(ell),
]
where (r) is the least residue. For every integer (x), this implies (|x|>B(ell)). Since (B(ell)ge36ell+88), and
[
x=2hquad(mathrm{LO/LE}),qquad x=4hquad(mathrm{RO/RE}),
]
we obtain the following uniform sector bounds:
- LO/LE: (|g|>|x|/2-9>18ell+35);
- RO: (|g|>|x|/2-1>18ell+43);
- RE: (|g|>|x|/2-2>18ell+42).

Thus (|g|>18ell+35). The same source depth estimates give (|T|le5ell+22), so for every (ellge1),
[
|g|>|T|.
]
Therefore the exact output-side test reduces to (mathrm{output left}iff g>0) directly from central-block nonmonochromaticity, without separately invoking the sector terminal-window widths or requiring (ellge3).

This is the preferred formulation for the phase automaton: prove the central x-block property, use the middle-block certificate to obtain (|x|>B), and then use the inequality above to select the exact next branch. The finite block property and the source depth wrapper remain the unresolved obligations.
