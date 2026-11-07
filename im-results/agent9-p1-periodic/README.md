# P1 inverse shadow: all positive-depth periodic tails excluded

**Status (7 November 2026):** The arbitrary-period reduction and the stepwise source-path extension are Lean 4.36.0-rc2 kernel-checked. [Run 42392999355](https://github.com/FlareZ123/bb6/actions/runs/42392999355) passed the factorization, all-period, eventual-tail, and repeated-block source-transport audit. [Run 42393598708](https://github.com/FlareZ123/bb6/actions/runs/42393598708) additionally compiled `SourcePeriodAllPeriods.lean`, which extracts exact finite-word runs from a genuine infinite `ShadowReach` trajectory and rules out every eventually periodic depth tail under the root-margin assumptions. Both audits reject `sorryAx` and Lean errors. Agent 3 independently reviewed the factorization and source-path arguments.

This is a substantive all-cost obstruction for the P1 inverse shadow. It does **not** decide P1, any BB(6) holdout, or BB(6).

## Main theorem

For any finite depth word `w : List Nat` containing at least one positive entry, there is no infinite exact scalar inverse ray that repeats `w` at every block:

```lean
PeriodWord.no_infinite_positive_depth_periodic_ray
  (L : Nat) (w : List Nat)
  (hp : ∃ t ∈ w, 0 < t)
  (m z : Nat → Nat)
  (hr : ∀ n, Run L w (m n) (z n) (m (n+1)) (z (n+1))) :
  False
```

The reindexed corollary `PeriodWord.no_eventually_periodic_positive_depth_ray` excludes the same pattern after any finite prefix. In `SourcePeriodWord.lean`, `source_periodic_tail_boundaries_reachable` transports every block boundary through the original `BB6.Precision.ShadowReach`, and `source_no_eventually_periodic_positive_depth_ray` exposes the source-level exclusion.

The existing Agent 13 source theorem separately excludes homogeneous zero-depth tails. Thus the positive-depth theorem closes the arbitrary finite-period case; the zero-depth homogeneous case remains covered by the earlier source result. Aperiodic inverse histories remain open.

## Proof architecture

1. **Exact marker decoding and factorization.** In [PeriodFactorization.lean](PeriodFactorization.lean), `factor_word_of_rotation_period` proves that if (dmid S), (0<d<S), (H=operatorname{weight}(w)<2^S-1), and
   [
   2^dHequiv Hpmod{2^S-1},
   ]
   then (w) is an exact repetition of a shorter word (u), with (operatorname{cost}(u)=d) and (operatorname{weight}(u)<2^d-1). The proof constructs a canonical binary decoder, proves its cost/weight inverse law, and obtains the quotient bounds (2^{d-1}le q<2^d-1). It does not assume a bound on the word cost or depth.

2. **Minimal marker return.** [PeriodMarkerMinimal.lean](PeriodMarkerMinimal.lean) supplies a shortest positive rotation period (d) dividing (S), from the integral slope relation and the finite deterministic rotation orbit.

3. **Primitive reduction.** The minimality of (d) implies the shorter word (u) is primitive: any smaller marker return of (u) lifts, by the exact repeated-weight and repeated-modulus formulas, to a smaller return of (w).

4. **Affine contradiction.** [PeriodFactorization.lean](PeriodFactorization.lean) proves the exact repeated-block weight and offset formulas. The infinite-run affine recurrence forces
   [
   (2^S-1)(z_1-z_0)=H S.
   ]
   The primitive word's all-cost divisibility obstruction, combined with [PeriodSecondary.lean](PeriodSecondary.lean)'s repeated affine obstruction, contradicts this equation and the initial block equation.

5. **Original-source connection.** [SourcePeriodWord.lean](SourcePeriodWord.lean) proves every repeated block boundary remains in the unmodified source `ShadowReach` relation and exports the eventual-periodic exclusion.

## Formal modules

- [PeriodFactorization.lean](PeriodFactorization.lean): exact marker decoder, arbitrary nonprimitive factorization, repeated weight/offset formulas, periodic affine recurrence, and primitive repeated-ray exclusion.
- [PeriodAllPeriods.lean](PeriodAllPeriods.lean): minimal-return reduction to a primitive word; no infinite positive-depth periodic ray; no eventual positive-depth periodic tail.
- [SourcePeriodWord.lean](SourcePeriodWord.lean): repeated-block `ShadowReach` boundary transport and source-level tail corollary.
- [SourcePeriodAllPeriods.lean](SourcePeriodAllPeriods.lean): stepwise infinite `ShadowReach` path extraction, root-margin propagation, and exclusion of all eventually periodic depth tails.
- [PeriodPrimitive.lean](PeriodPrimitive.lean): all-cost primitive marker obstruction.
- [PeriodSecondary.lean](PeriodSecondary.lean): repeated affine obstruction.
- [PaperProof.md](PaperProof.md): preserved earlier order-based paper argument and historical context.

## Relation to prior work

Agent 13's [BlockPotential.lean](../agent13-p1-adaptive-param/BlockPotential.lean) already established the affine-block potential and an abstract obstruction for a fixed block. [AlternatingDepth.lean](../agent13-p1-adaptive-param/AlternatingDepth.lean) treated the two mixed words `[0,1]` and `[1,0]`; [BlockSecondary.lean](../agent13-p1-adaptive-param/BlockSecondary.lean) supplied a secondary modular obstruction. The finite scan in [periodic_word_modular.py](../agent13-p1-adaptive-param/periodic_word_modular.py) covers total cost at most 2048.

The new contribution closes the all-cost nonprimitive-period gap: any admissible marker return yields an actual shorter depth list, which can then be ruled out by the primitive obstruction. It is not merely a finite scan or a proof for a preselected family of words.

## Stepwise source-path theorem

[SourcePeriodAllPeriods.lean](SourcePeriodAllPeriods.lean) closes the reverse extraction gap left by the repeated-block transport above. It defines an `InfiniteShadowPath` as a coherent sequence of actual `ShadowReach.step` witnesses:
`z_n=2^{t_n}v_n`,
`2z_{n+1}+1=L+m_n+t_n+v_n`,
and `m_{n+1}=m_n+t_n+1`,
starting from a state reachable from root (r).

**Theorem.** If (L\ge8), (0<r), and (r+4\le L), no such infinite path has an eventually periodic depth sequence, including an all-zero periodic tail.

- If the period word contains a positive depth, induction over the list constructs an exact `PeriodWord.Run` for each period block. The all-period theorem gives a contradiction.
- If the period word is all zero, `ShadowAlgebra.shadow_step_preserves_offset` propagates (z_n+4\le L+m_n). The gap (D_n=L+m_n-z_n\ge4) then satisfies (2D_{n+1}=D_n+3), so it decreases strictly forever, impossible in (mathbb N).

This is a statement about genuine stepwise paths in the abstract source `ShadowReach` relation under the displayed root margin. It does not show that every nonhalting P1 machine execution is eventually periodic or exclude aperiodic paths. The source audit is [run 42393598708](https://github.com/FlareZ123/bb6/actions/runs/42393598708); the printed axiom lists contain only standard Lean axioms and no `sorryAx`.

## Remaining mathematical gap

The result excludes eventually periodic positive-depth inverse tails. It does not prove that every infinite inverse history is eventually periodic, and it gives no contradiction for a genuinely aperiodic sequence of varying depth words. The next research target is a uniform obstruction for arbitrary varying blocks, using the exact affine recurrence and source feeder margins. Until that gap is closed, the P1 decision and the exact value of BB(6) remain open.
