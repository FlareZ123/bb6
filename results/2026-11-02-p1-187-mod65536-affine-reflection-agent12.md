# 187 new source-verified P1 critical-index families modulo 65536

Agent 12, 2026-11-02. **Rigorous intermediate mathematical result; P1 and BB(6) remain undecided.**

## Certified theorem

For the original P1 blank-entry acceleration `BB6.Agent1.Reach` beginning at `(2,1)`, let `extraResidues` be the exact list of 187 distinct natural numbers in [P1RAffineAggregate.lean](../im-results/agent12-backwards/P1RAffineAggregate.lean).

Lean proves:

```lean
BB6.Agent12Affine.blank_no_critical_extra (R q : Nat)
    (h : R ∈ extraResidues) :
    ¬ BB6.Agent1.Reach 2
       (14*2^(65536*q+R)-2*(65536*q+R)-10)
```

For every listed R and every q, the actual accelerated blank-start orbit never reaches that critical halting index. Source-level [Lean CI 41529652730](https://github.com/FlareZ123/bb6/actions/runs/41529652730) passed with final theorem axioms **`[propext, Classical.choice, Quot.sound]`** and no `sorryAx`. The listed residues are outside all 36 Agent47 certified modulo1024 families, so these are 187 new, disjoint modulo65536 exclusions. The list's 187 count and pairwise distinctness, and disjointness from the 36 old parent classes, are separately proved by decidable arithmetic within the aggregate source. The 187 families occupy 25 of the 28 previously unresolved modulo1024 parent residues; the other three parent residues are 286, 334, 494 modulo1024.

## Source-connected proof mechanism

Put `n=65536*q+R`, `W=2^(n-16)`, `S=7*W-q-1`. The necessary critical precursor hub is

`(14*2^n-2*n-16,3) = (131072*S+131072-2*R-16,3)`.

The coefficient-level `goodAff` checker exhausts positive-output `GAncestor` inverses and constructs finite `Blocked` proof trees. Every terminal branch contradicts either an established global mod4 invariant or the exact even-hub `14*2^j` power-shape invariant. The source-proved power gap and `W≥64(q+1)` make all terminal checks valid for **every q**. Universal `goodAff_sound_general` proves the checker sound against unmodified source definitions; the aggregate theorem simply kernel-evaluates the finite Boolean checks using `decide +kernel` and imports the already proved soundness. Its recursive fuel bounds inverse-proof depth, with no bound on forward Turing-machine steps.

Original-source dependencies: Agent1 `GAncestor` and its reachability invariants, Agent47 `inverseAt` completeness and depth bound, Agent4 `Blocked` soundness, and Agent50 critical-to-hub reduction. In the same CI, `goodAff_sound_general` and each named individual R=382,542,574,942 result compiled with standard Lean axioms only.

## Reproducibility

- [Exact 187-element source list and final theorem](../im-results/agent12-backwards/P1RAffineAggregate.lean).
- [General all-q power gap and identity](../im-results/agent12-backwards/P1RAffineGeneralGap.lean).
- [Packed generic affine-reflection source](../im-results/agent12-backwards/P1RAffineGeneral.lean.xz.b64), pinned decompressed SHA-256 `d627ad7ee677c7f6e2ef06941167cc148501f4a973ed0850c74f2b6aed40bf0b`.
- [Original packed affine checker](../im-results/agent12-backwards/P1R382AffineReflection.lean.xz.b64), decompressed SHA-256 `ca916346fe599eeafbad9a21309df89180daa756918afc82e42d405ecedd4b36`, with deterministic source-level patch `patch_p1_r382_proof.py`.
- [Manual CI workflow](../.github/workflows/agent12-p1-lean-verify.yml), [successful original-source run 41529652730](https://github.com/FlareZ123/bb6/actions/runs/41529652730).

This aggregate supersedes the earlier [single n=382 infinite-family certificate](./2026-11-02-p1-r382-mod65536-reflective-inverse-agent12.md). It extends and credits Agent47's 36 modulo1024 original-source certificates and Agent28's inverse-cone computational prototype.

## Research scope

The result is a genuine **partial** all-time exclusion of 187 infinite critical-index families. It does not prove the P1 machine nonhalting, exclude every possible P1 halting critical index, determine the status of any other rooted BB(6) holdout, provide a universal six-state upper bound, or determine exact BB(6). Progress requires stronger global invariants or complete parameter-dependent inverse closure, especially for the still-surviving P1 n≡2(mod16) and n≡14(mod16) families.
