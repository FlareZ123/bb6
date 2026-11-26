# Six 1LE leaves: binary carry with growing right sweep

The theorem `BB6.Agent11Raw391LEBinarySix.never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m` is locally kernel-checked (Lean 4.36.0-rc2; propext and Quot.sound only).

| Variant | normalized-open index | Partial table |
|---|---:|---|
| a | 1897 | 1RB1LE1RC1LB0RD0RC1LD0RA0LA0LF1RA--- |
| b | 2372 | 1RB1LE1RC1RF0RD0RC1LD0RA0LA1LB---1LE |
| c | 2529 | 1RB1LE1RC1LB0RD0RC1LD0RA0LA1LF1LA--- |
| d | 2534 | 1RB1LE1RC0RE0RD0RC1LD0RA0LA1LF1LB--- |
| e | 2535 | 1RB1LE1RC1LB0RD0RC1LD0RA0LA1LF1LB--- |
| f | 2550 | 1RB1LE1RC1LB0RD0RC1LD0RA0LA1LF1RB--- |

At D1 checkpoints, the near-first left list is one of three finite mode prefixes followed by an arbitrary finite binary word P, and the right list is a unary run of at least two ones. The A and B stages rewrite the prefix and increase the right run by two and one. The C stage enters B and transfers the maximal initial run of ones in P into the right seed; the first zero or implicit blank is changed to one, the carried ones become zeros, and the A prefix is restored. The finite frame is variant-specific, but all arbitrary-tail sweeps and the return-to-D1 theorem are shared. The C stage increases the right run by three. The unrestricted-tail induction does not assume a maximum counter width or run length.

This discharges six more candidate residuals, but the complete 1LE child Cover is not yet proved. Leaves 1837 and 2370 are related but not covered by this theorem (paired-bit carry and lookahead carry, respectively).
