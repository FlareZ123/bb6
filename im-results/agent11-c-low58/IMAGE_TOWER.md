# Machine C: exact ancestral image hierarchy at arbitrary depth

**Mathematical result, 9 November 2026.** For the unmodified first-return section map (F=`BB6.Agent46.secNext`, every integer (n\ge0) has a **positive-density infinite cylinder of states with exactly (n) levels of possible successful section ancestry**. These states never appear on the true blank-derived section orbit from ((5,1)). The theorem is structural and root-sensitive; it does not decide the Machine C halting problem or BB(6).

## Precise source theorem

Define (I_n={p:exists q_0,\ldots,q_n,\ F(q_i)=q_{i+1}\text{ for }i<n,\ q_n=p}), with (I_0=\mathbb N^2). For (t\ge0), set
[
b_0(t)=4t+5,\quad b_{n+1}(t)=2b_n(t)+2,
\qquad b_n(t)+2=(4t+7)2^n.
]
Set (r_0=1,r_1=7,r_2=7), and (r_{n+3}=10-r_{n+2}); thus (r_n=3) for odd (n\ge3) and (r_n=7) for even (n\ge2).

For **all** (n,t,x\in\mathbb N) with (x\ge8) and (x\equiv r_n\pmod8), put (p=(x,b_n(t))). Then
[
\boxed{p\in I_n\setminus I_{n+1}
\quad\text{and}\quad
\forall s\ge0,\ F^s(5,1)\ne p.}
]
The second assertion treats failed section transitions as absorbing failure, as in the original `GenericSection.run`.

For each fixed (n), this cylinder is a single residue class (x\bmod8,;y\bmod2^{n+2}) up to finite coordinate cutoffs. Its **natural density in expanding square counter grids is exactly (2^{-(n+5)})**. Consequently every inclusion (I_{n+1}\subsetneq I_n) is strict, with a positive-density difference. The (n=2) case overlaps the previously certified `I_2\setminus I_3` sectors of Agent 34; the contribution here is one source-checked inductive construction for *every* finite inverse depth plus the explicit genuine-root exclusion.

## Proof mechanism and why the quantifiers are unbounded

The original-source exact predecessor grammar proves the following uniqueness statement for any output ((x,y)) with (y\ge6) even and ((x+y)\bmod8\in\{1,3,5\}):
[
F(a,k)=(x,y)
\quad\Longleftrightarrow\quad
(a,k)=D(x,y):=(x+y-2,(y-2)/2).
]
The forward direction uses the source-certified valuation-one converse for residues 1 and 5, and the source-certified `only_direct` theorem for residue 3; the reverse direction is the genuine original direct section transition. No truncated inverse enumeration or quotient abstraction is used.

Every target ((x,y)) with (y\ge5) odd and ((x+y)\bmod4=2) has **no** original section predecessor at all, by `BB6.Agent3.section_odd_image`.

Define `cone 0` to consist of those missing-image targets. Recursively `cone (n+1)` consists of targets in the above unique-direct sector whose direct parent is in `cone n`. Structural induction proves that every `cone n` target has an (n)-step predecessor chain and has no chain of length (n+1). A second induction on (n) and genuine run time proves such targets cannot appear on the original blank section: at time zero their right counter is at least five whereas the root counter is one; at positive time the unique parent is again in the lower-depth cone.

For the explicit family, (D(x,b_{n+1}(t))=(x+2b_n(t),b_n(t))). The phase sequence (r_n) ensures (x+2b_n(t)\equiv r_n\pmod8) whenever (x\equiv r_{n+1}\pmod8); this closes the induction for every (n,t,x). The right-counter formula establishes the density count.

## Reproducible formal source chain

- [Arithmetic and all-depth family](TowerArithmetic.lean): `b_closed`, `cylinder_cone`, and phase recurrence. Compiled locally in Lean **4.36.0-rc2**, axiom audit `[propext, Quot.sound]`.
- [Source-connected theorem](SourceImageTower.lean): `unique_direct`, `exact_depth`, `cone_blank_unreachable`, `strict_every_depth`. Imports `ThreeConeProper`, `ValuationOneOrbit`, and `Agent3CImage` from prior original-source certified work.
- [Existing selective manual source workflow](../../.github/workflows/agent34-c-source-cone.yml) compiles the unchanged original `secNext` and all dependencies, including source-hash-restored valuation-one theorem. The first source check passed [run 42552332192](https://github.com/FlareZ123/bb6/actions/runs/42552332192) for the abstract recursive `exact_depth` module; the updated **explicit positive-density plus genuine-root** source check is [run 42552988741](https://github.com/FlareZ123/bb6/actions/runs/42552988741), whose outcome must be inspected before describing the new aggregate theorem as fully source certified. Local arithmetic compilation is separate from original-source integration.

## Mathematical boundary and next step

This theorem supplies *all-time* genuine blank-origin exclusions, but does **not** cover all possible stopping targets. The earlier [all-depth Machine C late-three-cone](../agent19-c-odd-dyadic/README.md) and Agent 34’s [strict two-versus-three image example](../../results/2026-11-08-machine-c-exact-two-step-image-density-agent34.md) should be compared for any proposed stopping-locus corollary. In particular, do not assert an independently new halting-residue exclusion from this construction without first testing whether it is implied by the canonical merged high-stopping predicate.

The useful remaining direction is to discover a forward-closed *authentic* root property that forces **every** low/high halting target into a missing ancestral image, or exhibit one source-checked reachable target. The existence of strict ancestry strata alone leaves the unbounded existential stopping parameters open.
