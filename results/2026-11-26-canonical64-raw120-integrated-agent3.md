# A source-accepted 64-residual weighted-TNF quotient reduction

**Status:** source-accepted conditional theorem; not an exact BB(6) solution.

## Main statement

Let the canonical champion-root-compatible six-state, two-symbol machine class be represented by the repository's weighted-TNF quotient. The integrated Canonical64 development proves

\[
\forall m,\ \mathrm{compatible}(\mathrm{root},m)
\Longrightarrow
\mathrm{WeightedBound}(6{,}766{,}859,m)
\ \lor\exists e\in R_{64},\ \mathrm{TNFQuotientCompatible}(e,m),
\]

where R64 is an explicitly constructed list of exactly 64 retained quotient representatives.

Consequently, for every B ≥ 6,766,859, if each of the 64 retained representatives has a Cover at weighted bound B, and a blank-start machine attains B, then the repository's conditional theorem ExactBB6 B follows. The 64 residual Covers and the attaining witness are hypotheses, not discharged obligations.

## Construction of the 64-entry roster

The reduction composes three source-audited stages:

1. **Canonical68:** the 76-entry quotient roster is reduced to 68 by the eight accepted E1 sibling-parent Covers. The conditional E1 interface is documented in [the Canonical68 result](2026-11-26-canonical68-E1-parent-reduction-agent6.md).
2. **Canonical65:** three further parent Covers, Raw71, Raw77 and Raw81, are consumed against the integrated 68-entry roster, leaving 65 representatives. The eleven-parent proof environment is source-audited in [CI run 45732489302](https://github.com/FlareZ123/bb6/actions/runs/45732489302), artifact 15078085872.
3. **Canonical64:** the Raw120 parent is removed from the 65-entry roster. Its exact weighted parent threshold is

\[
\forall m,\ \mathrm{compatible}(p_{120},m)\to
\mathrm{WeightedBound}(T,m)
\quad\Longleftrightarrow\quad 224{,}707\le T.
\]

The complete Raw120 Cover is lifted to the common floor 6,766,859 and composed with the integrated Canonical65 theorem.

The final Lean module is im-results/agent3-tnf-raw120/Canonical64Raw120Integrated.lean. It defines roster64 := removeParents [p120] roster65, proves p120_count and count64 = 64 by computation, establishes sound64_integrated, and derives the conditional exact_at_target theorem.

## Source acceptance and reproducibility

The final integrated consumer passed in [CI run 45750164590](https://github.com/FlareZ123/bb6/actions/runs/45750164590), at source revision 949fde331f10df81a968f157c622faa581597276. Its proof-closure artifact is raw120-canonical64-audit, artifact ID 15085029091, SHA-256 digest:

bb4fa3c190ab2a67e3f7c17f8e1c0f07c2215b282451a361501f8ff6c678d55b

The Raw120 parent source audit is [run 45733198942](https://github.com/FlareZ123/bb6/actions/runs/45733198942), artifact 15080392441. The integrated Canonical65 base is run 45732489302, artifact 15078085872. The integration uses the repository's reachable-import closure and kernel-declaration comparison; the final theorem profiles are checked against the standard axiom allowlist.

The source and integration driver are preserved under im-results/agent3-tnf-raw120/, including Canonical64Raw120Integrated.lean, assemble_raw120_canonical.py and the accompanying README.

## Significance and remaining work

This is a genuine reduction of the unresolved quotient frontier from 76 to 64 representatives, with twelve parent cuts composed into a single source-accepted conditional interface. It also establishes the sharp uniform weighted threshold 224,707 for Raw120, including the incoming blank delay and halt tick.

The result does **not** prove that the 64 retained representatives halt within the champion score, nor does it by itself establish a universal upper bound for BB(6). The next useful parent candidate is Raw112: its parent Cover at weighted bound 100,000 could remove one further representative if its independent source audit and an integrated composition against the exact Canonical64 roster both pass.
