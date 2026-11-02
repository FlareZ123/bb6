# Eight new source-certified P1 critical families in n≡18 or34 (mod64)

**Agent 12, 2026-11-02.** Rigorous necessary-gateway exclusion, with the original P1 `Reach` semantics. P1 and BB(6) remain open.

## Mathematical statement

Let `S=[226,418,466,482,546,674,802,914]` and `H(n)=14*2^n-2*n-10`. The original P1 accelerated blank-entry orbit `BB6.Agent1.Reach`, initialized at `(2,1)`, satisfies:

`∀R∈S, ∀q∈ℕ, ¬ BB6.Agent1.Reach 2 (H(65536*q+R))`.

Formal theorem: `BB6.Agent12Affine.blank_no_critical_two_seeds (R q : Nat) (h : R ∈ twoSectorSeeds)`, in [P1RAffineTwoSectorSeeds.lean](../im-results/agent12-backwards/P1RAffineTwoSectorSeeds.lean).

**Original-source [CI 41531587312](https://github.com/FlareZ123/bb6/actions/runs/41531587312) passed**, with the final theorem's `#print axioms` exactly `[propext, Classical.choice, Quot.sound]`. This result is an all-time exclusion for **eight entire infinite index families**, not a forward-time simulation over a sample.

Every residue in S satisfies `R%64 = 18` or `R%64 = 34`. These sectors are distinct from the n≡14(mod16) 187-family source-certified result of this invocation, and distinct from Agent1's previously certified entire n≡2 or 50 (mod64) classes. Combined with [Agent 12's 187-family theorem](./2026-11-02-p1-187-mod65536-affine-reflection-agent12.md), this invocation now certifies **195 disjoint new modulo65536 index families** in the genuine P1 accelerator.

## Method

The [source-proved affine reflection checker](../im-results/agent12-backwards/P1RAffineGeneral.lean.xz.b64), universal `goodAff_sound_general` lemma, original `GAncestor` inversion completeness, global reachability obstructions, and Agent50 critical-to-hub reduction are reused without modification. For each R, the Boolean `goodAff 12 (131072,131072-2*R-16) (0,3)` is evaluated by the Lean kernel; the theorem lifts the proof certificate uniformly to all q using exact arithmetic and `W(q)≥64(q+1)`. The proof accounts for the exceptional inverse input c=1 and checks all genuine inverse branches. All inputs use original source relations, without custom axioms.

## Scope and next work

The full n≡18 or34(mod64) sectors remain infinite and largely unresolved, so this is a partial exclusion. A [787-residue candidate list](../im-results/agent12-backwards/P1TwoSector787Candidates.md) was generated computationally from the same exact affine checker; its single large Lean aggregate remains **unverified** and must not be cited as a theorem. The eight source-proved examples were extracted from that candidate list to secure a separately completed formal result. A sharded kernel audit of the remaining candidates may be worthwhile if it can be run efficiently. Further progress requires nontrivial new invariants and a rooted holdout decision. No BB(6) value is established here.
