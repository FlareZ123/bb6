# Agent 14 independent check of Agent 16's five Sheep E inverse cones (2026-11-04)

**Scope and status.** This is an independent finite-arithmetic corroboration of the five infinite-progressions reported in [Agent 16's certificate](../agent16-sheep-new-even-cones/README.md), together with a simpler, fully kernel-checked **abstract exceptional-power exclusion lemma**. It is *not* independent original-machine source integration, not an all-family Lean cone theorem, and not a Sheep nonhalting or BB(6) result. The five progressions were already reported by Agent 16; no new excluded family or mathematical frontier priority is claimed.

The independently implemented checker does not import Agent 16's certificate program. It defines the literal even-section return, exact generic inversion, multiplicative-order enumeration by repeated doubling, modular full-period checks, high-valuation induction premises, and exact symbolic child identities. All five sets of reported graph nodes, each complete low-valuation row, and each original-source-shaped exceptional row matched:

| Exponents | Nodes | Genuine generic edges | Hidden h rows | Low-a rows | Full-period samples |
| --- | ---: | ---: | ---: | ---: | ---: |
| j=118+14580k | 3 | 2 | 6 | 51 | 182 |
| j=246+24300k | 5 | 4 | 11 | 102 | 346 |
| j=558+8100k | 4 | 3 | 8 | 60 | 168 |
| j=846+8100k | 5 | 4 | 9 | 76 | 286 |
| j=702+11340k | 4 | 3 | 10 | 82 | 229 |
| **Total** | **21** | **16** | **44** | **371** | **1211** |

The independently calculated exact DAG edges reproduce every listed Agent 16 edge, and the supplementary literal E(x)=y test succeeded for each at k=0 and k=1. All symbolic nodes were checked to be distinct for every k≥0 and outside the genuine even-section seed 10; the five arithmetic progressions were pairwise disjoint. This validates the **finite premises** of the paper inverse-basin argument, conditional on the previously authenticated even-section semantics and the ordinary mathematical proof of modular and valuation reductions.

## A shorter universal exceptional-predecessor exclusion

For each rational node Y(j)=(2^(j+s)+b)/d and each permitted 3-adic exponent h, the Sheep special case x=3·2^a forces

    (3D)·2^a + D·a + C = 2^(j+s+h),
    D=d·3^h, C=2D+2^h(d-b).

Put A=3D, choose e with 2^e<A<2^(e+1), and L=2^(e+1)-A. Set t=j+s+h-e-1. If t≥t0≥1 and

    D·t0+C < L·2^t0,

then **no natural a** can solve the equation, for any larger j. Proof: the inequality persists because its exponential side doubles while its linear side grows by D. If a≤t, the putative left side is less than (A+L)·2^t=2^(j+s+h). If a≥t+1, its leading term alone exceeds the target, since A>2^e. Every one of the 44 node/h rows satisfies the base condition, with C>0. This eliminates the two-sided exception-gap computation required by the earlier certificate for these rows.

The reusable source-independent Lean module [IndependentExceptionalGap.lean](IndependentExceptionalGap.lean) proves both the global exponential/linear inequality and the all-a exclusion, with **no sorry**, by compiling under Lean 4.36.0-rc2. Both axiom audits print only [propext, Quot.sound]. Source SHA256 (LF text) is ac5dd9ee814043ea66708777f934f98a0e90c618ebacb7ccf6894529b834e3db.

**Remaining work.** Preserve the independent checker source and hash, certify the 44 base inequalities in Lean using original-source inverse equations, then integrate a finite-DAG soundness theorem for the five actual original-machine-gate exclusions. The overarching outstanding mathematical problem is a seed-sensitive global obstruction to every remaining Sheep power target. Neither the five finite basins nor this local gap lemma proves such an obstruction.
