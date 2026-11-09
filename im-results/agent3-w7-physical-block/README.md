# W7-2: physical-source all-length block sweeps

**Agent 3, 9 November 2026. Status: intermediate proof infrastructure; neither historic rooted holdout is decided.**

## Genuine-root target

Original six-state, two-symbol table: 1RB1LB_1RC0LA_1RD0RE_1LA0LB_1RF---_1RB1LD.

Historic October 24 holdout row 146 starts this table in A. Historic row 411 is its reflected and renamed **D-start**, linked by the source-certified root-sensitive theorem in [Agent 29's Row146Conjugacy.lean](../agent29-roster-six-audit/Row146Conjugacy.lean).

[Dennis Koshta's dated *informal* proof](https://github.com/DennisKoshta/denniskoshta-portfolio/blob/b48bd32fab8b476135d47ffa4e5f9bfb9a80d8c7/public/busy-beaver/machines/1RB1LB_1RC0LA_1RD0RE_1LA0LB_1RF---_1RB1LD/proof.md.html) proposes nonhalting of both roots via eventual entry into two exact symbolic cycles N(Y) ↦ N(2^18 Y + 32859022) and Q(W) ↦ Q(2^18 W + 34431880). Those large cycle claims are unformalized. Historical roster removal alone does not determine any rooted outcome.

## Completed source-table mathematical theorems

[Row146Block.lean](Row146Block.lean) imports the **unchanged** Agent 29 raw-source transition table and its infinite physical tape. It kernel-proves exact, all-length, full-physical-tape transformations for all integer head positions, all natural exponents n, and every arbitrary ambient tape.

| Block input | Block output | Exact raw steps |
| --- | --- | --- |
| B> 0100^n | 1011^n B> | 4n |
| C> 1000^n | 0111^n C> | 4n |
| E> 0001^n | 1110^n E> | 4n |
| F> 0010^n | 1101^n F> | 4n |
| 0111^n <A | <A 0100^n | 14n |
| 1111^n <A | <A 0101^n | 4n |
| 1111^n <B | <B 1010^n | 4n |

Here > reads the first cell to the right; < reads the last cell to the left. The functions putR and putL replace precisely these n disjoint blocks and preserve every other cell from any surrounding tape. The raw-run equality with result some proves no undefined transition occurs during these exact steps. There are no assumptions on blank suffixes, finite tape supports or upper bounds for n.

Each proof is built from seven direct finite original-table runs, a whole-tape translation theorem, commutativity of disjoint four-cell writes, and parametric induction theorems sweepR and sweepL. Public Lean theorems: physical_b_0100_1011, physical_c_1000_0111, physical_e_0001_1110, physical_f_0010_1101, physical_a_0111_0100, physical_a_1111_0101, physical_b_1111_1010.

A local Lean 4.36.0-rc2 build on a literal matching source definition completed without errors or sorry, with only standard axioms [propext, Classical.choice, Quot.sound]. The [manual original-source CI](https://github.com/FlareZ123/bb6/actions/workflows/agent29-row146-conjugacy.yml) rebuilds the unchanged original Row146Conjugacy module and imports it for this proof. Check the CI result before claiming that the *imported* source is verified remotely.

## Unresolved decisive obligations

These seven shifts are the elementary symbolic-rewrite rules in the external author's argument. This new contribution supplies an independent full-physical-tape Lean bridge, **not** a classification of either blank-start machine. The reported N/Q cycles each use about 180,000 symbolic moves and about 6,900 Diff-rule applications; the D-cycle, both opening runs and their composition also need a sound reflective replay. A small verified Diff-rule checker, coupled to this source bridge, would be far more consequential than more finite-prefix simulations.

Keep this in im-results/ until a genuine BB(6) machine outcome has a complete and reviewable original-source proof.
