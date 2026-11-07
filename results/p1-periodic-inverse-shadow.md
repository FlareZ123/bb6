# No eventually periodic positive-depth inverse rays in the P1 scalar shadow

## Result

Let (Linmathbb N), let (w) be a finite list of inverse depths containing at least one positive entry, and let (m,z:mathbb N	omathbb N). Write (operatorname{Run}(L,w,m,z,m',z')) for the exact finite-word scalar predecessor relation used by the P1 inverse shadow.

**Theorem.** There is no infinite sequence of consecutive copies of (w):
[
left(orall n, 
operatorname{Run}(L,w,m_n,z_n,m_{n+1},z_{n+1})ight)
quadLongrightarrowquad ot.
]
More generally, no such repeated block can begin after a finite prefix. In particular, the P1 scalar shadow admits no eventually periodic inverse-depth tail whose period contains a positive depth.

The theorem is formalized as `PeriodWord.no_infinite_positive_depth_periodic_ray` and `PeriodWord.no_eventually_periodic_positive_depth_ray`. The source module `BB6.Agent9PeriodSource` additionally proves that every block boundary of a hypothetical repeated tail remains in the unchanged `BB6.Precision.ShadowReach` relation and exports `source_no_eventually_periodic_positive_depth_ray`.

The all-zero homogeneous case is covered separately by Agent 13's source-verified homogeneous-ray exclusion. The stepwise source-path theorem below also rules out an all-zero eventual-periodic tail under its stated root-margin assumptions. This result does not rule out genuinely aperiodic inverse histories and does not decide P1 or BB(6).

## Proof

Put (S=operatorname{cost}(w)), (H=operatorname{weight}(w)), (A=2^S), and (D=operatorname{offset}(w)). The exact wordwise scalar recurrence gives, for each block boundary,
[
A z_{n+1}=z_n+H(L+m_0)+HSn+D.
]
The integer affine-difference lemma implies that (Q=z_1-z_0) satisfies
[
(A-1)Q=HS.
]
Since (w) contains a positive depth, the marker bounds give (0<H<A-1). Hence (0<Q<S), and (Q) is an integer.

The cyclic marker-rotation theorem then supplies a least positive return (d<S) with (dmid S) and
[
2^dHequiv Hpmod{A-1}.
]
The exact factorization theorem proves that (w=u^k) for some (k>0), where
[
operatorname{cost}(u)=d,qquad
operatorname{weight}(u)<2^d-1.
]
Minimality of (d) forces (u) to be primitive: any smaller marker return of (u) lifts through the exact repeated-weight and repeated-modulus identities to a smaller return of (w).

The infinite affine recurrence for (w=u^k), together with the exact repeated offset formula, now satisfies the hypotheses of the primitive repeated-affine obstruction. That obstruction contradicts the primitive divisibility failure
[
(2^{operatorname{cost}(u)}-1)
mid
operatorname{weight}(u)operatorname{cost}(u).
]
Thus no infinite repeated positive-depth word exists. Reindexing the scalar functions proves the eventual-tail version.

## Formal verification and provenance

- Lean version: **4.36.0-rc2**.
- GitHub Actions verification: [run 42392999355](https://github.com/FlareZ123/bb6/actions/runs/42392999355), including the dedicated arbitrary-word and original-source `ShadowReach` audit.
- The workflow prints axiom dependencies and rejects `sorryAx` and Lean errors; the audited run passed.
- Agent 3 independently reviewed the quotient bounds, canonical marker decoder, and rotation-lifting argument.

Supporting formal files:

- `im-results/agent9-p1-periodic/PeriodFactorization.lean`: exact binary decoder, marker factorization, repeated weight and offset formulas, and primitive repeated-ray obstruction.
- `im-results/agent9-p1-periodic/PeriodAllPeriods.lean`: minimal-return reduction and all-period / eventual-tail theorems.
- `im-results/agent9-p1-periodic/SourcePeriodWord.lean`: original-source reachability transport and source-level corollary.
- `im-results/agent9-p1-periodic/PeriodPrimitive.lean` and `PeriodSecondary.lean`: primitive divisibility and repeated affine obstructions.

## Stepwise source-path strengthening

The fixed-word theorem can be applied directly to a genuine infinite trajectory in the original `BB6.Precision.ShadowReach` relation.

Let (L,r\in\mathbb N) satisfy (L\ge8), (0<r), and (r+4\le L). An `InfiniteShadowPath` consists of sequences (m_n,z_n,t_n,v_n\in\mathbb N) with an initial state reachable from the root (r), and
\[
z_n=2^{t_n}v_n,\qquad
2z_{n+1}+1=L+m_n+t_n+v_n,\qquad
m_{n+1}=m_n+t_n+1.
\]
**Theorem.** The depth sequence ((t_n)) cannot be eventually periodic.

For a period word containing a positive entry, induction over each finite block constructs the exact `PeriodWord.Run` relation. The all-period obstruction then gives a contradiction. If the period word is all zero, the source margin is propagated by `shadow_step_preserves_offset`. With (D_n=L+m_n-z_n\ge4), a zero-depth step satisfies
\[
2D_{n+1}=D_n+3,
\]
so (D_{n+1}<D_n), which cannot hold forever in (mathbb N).

This closes the stepwise extraction gap from an infinite `ShadowReach` trajectory to repeated finite-word runs. The theorem is formalized in `BB6.Precision.InfiniteShadowPath.no_eventually_periodic_shadow_path` in `im-results/agent9-p1-periodic/SourcePeriodAllPeriods.lean`. It is conditional on an actual infinite trajectory with the displayed step witnesses and the root margin; it does not establish that every nonhalting P1 execution yields such a trajectory.

The source-path audit is [GitHub Actions run 42393598708](https://github.com/FlareZ123/bb6/actions/runs/42393598708). Lean 4.36.0-rc2 compiled the module and printed the axiom dependencies for the positive-depth, zero-depth, and combined theorems. The audit passed without `sorryAx` or Lean errors; the remaining dependencies are standard Lean axioms.

## Scope

The theorem rules out eventually periodic positive-depth inverse-depth sequences. It does not prove that every infinite inverse history is eventually periodic. Aperiodic histories with varying depth words remain open, and no exact value or new numerical bound for BB(6) is claimed.
