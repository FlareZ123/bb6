# Sheep: exact eighth 3-adic stratum power-parent census

**Agent 40, 16 November 2026. Intermediate original-source theorem; not a BB(6) solution.**

For the authentic first-even return graph of the Sheep machine

`1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`,

consider powers (Y=2^j) with

[
j=4374t=2cdot3^7t,qquad t\ge1,quad 3\nmid t.
]

Then (v_3(j)=7) and LTE gives (v_3(2^j-1)=8). The complete legal generic even-source predecessor census has **exactly four** sectors:

| Hidden odd steps (h) | Source valuation (a) | Exact existence condition |
|---:|---:|---|
| 1 | 1 | (t\equiv1\pmod2) |
| 1 | 3 | (t\equiv2\pmod4) |
| 3 | 6 | (t\equiv4\pmod7) |
| 8 | 2 | (t\equiv5\pmod9) |

There are no other generic sources. The exceptional odd-part-three source is excluded for every (a\ge1) and every (0\le h\le8).

## New authentic blank-root exclusion

The new Lean theorem `blank_even_cannot_hit_eighth` proves, for every (t\ge1),

[
3\nmid t,\quad t\equiv0\pmod4,\quad
t\not\equiv4\pmod7,\quad t\not\equiv5\pmod9
\quad\Longrightarrow\quad
\neg\operatorname{EvenReach}(10,2^{4374t}).
]

The argument is an exact last-edge contradiction in the original-source Sheep return graph: any nontrivial path from the genuine blank entry 10 to a larger power must have one of the two complete inverse forms (generic or exceptional). The generic forms reduce to the four residue sectors above, all incompatible with the displayed root-free conditions; the exceptional form is ruled out by a uniform exponential gap.

The conditions define **30 residue classes modulo 252**:

`8,16,20,28,40,44,52,56,64,76,80,92,100,112,124,128,136,148,152,160,164,184,188,196,208,220,224,232,236,244`.

Among the 168 classes with (3\nmid t), this is density

[
\frac{30}{168}=\boxed{\frac5{28}}.
]

Equivalently it is (5/42) among all (t) modulo 252. Since the stratum (j=4374t), (3\nmid t), has natural density (1/6561) among all exponent indices, the excluded subfamily has natural density (5/183708) among all (j). For example, (t=8) gives (j=34992), and (2^{34992}) is unreachable from the genuine blank entry.

This is an infinite all-time exclusion of a specified family of candidate halting powers. It does **not** prove that Sheep never reaches any other power, does not decide the Sheep machine, and does not determine BB(6).

## Proof architecture and reproducibility

- **Hidden-length bound:** (2^{4374}\equiv6562\pmod{3^9}), (2^{8748}\equiv13123\pmod{3^9}), and (2^{13122}\equiv1\pmod{3^9}). Thus (2^{4374t}\not\equiv1\pmod{3^9}) whenever (3\nmid t), so every inverse edge has (h\le8).
- **Generic valuation cutoff:** for (h=0), (a\ge2) is excluded; for (1\le h\le8), all (a\ge2h+3) are excluded by the signed-power gap theorem. This leaves 89 ((h,a)) pairs.
- **Exact modular census:** for each pair, the period of (2^{4374}) modulo (3^h(2^{a+1}+1)) is computed and checked. The certificate covers 772 complete period representatives, with maximum period 57. Exactly the four rows in the table survive.
- **Exceptional source:** a uniform exponential-dominance argument excludes odd source cofactor (v=3) for all (a), all (h\le8), and every (t\ge1).
- **Original-source proof:** `SheepEvenReachInverse.blank_even_inverse_cases` splits every genuine last edge of the actual blank-even return graph into the generic and exceptional Diophantine equations. The final theorem imports that exact source module; it does not replace the original machine by a simulator or a surrogate recurrence.

Run `python3 certificate.py` to reproduce the modular periods, all 772 residues, the four surviving families, the exceptional-gap margins, and the exact 30 root-free classes. The accompanying manual-only workflow compiles the theorem against the pinned upstream DeepMind Sheep source and rejects any transitive `sorryAx`.

## Relation to adjacent research

This is the **eighth** 3-adic target stratum (v_3(2^j-1)=8), distinct from Agent 17's seventh-stratum target (j=1458t) and Agent 40's sixth-stratum target (j=486t). It is also disjoint in 3-adic valuation from the earlier fourth/fifth target strata. Agent 14's mixed h=8 predecessor corridors concern particular (t\equiv0\pmod4) progressions; the present theorem isolates the complementary (t\equiv0\pmod4) residue classes not admitted by any of the four direct-parent sectors.

All material remains in `im-results/`; external academic novelty has not been established.
