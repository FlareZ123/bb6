# Raw39 1LE four siblings: two-block affine growth

Four normalized open leaves: 15741 `1RB1LE_1RC0LB_0RD0RF_1LD0RA_1LB0RA_---1RA`; 15742 `1RB1LE_1RC0LB_0RD0RF_1LD0RA_1LB1LB_---1RA`; 15743 `1RB1LE_1RC0LB_0RD0RF_1LD0RA_1LB1LC_---1RA`; 22215 `1RB1LE_1RC0LB_0RD0RF_1LD0RA_1RA1LB_---1RA`. F0 is undefined. The exact blank entry costs are 2207, 1991, 2423, 2257 respectively.

Use zipper state F (scanned 1, left including scanned cell 101) with right word PA I^n S0 J^n Vtail. Here I=00111, J=011, PA=1111000111000111000111111, PB=1000111000111000111000000111, S0=0011100111001111110111, S1=001110011100000111011, S2=00111001110011100000111011, S3=S0 J, Vtail=011111. Four transitions:
1. PA I^n S0 R -> PB I^n S1 R.
2. PB R -> PA I R, with I S1=S2.
3. PA I^n S2 R -> PB I^n S3 R.
4. PB R -> PA I R, yielding family(n+1) because S3=S0 J.

The variable forward sweep transfers I to left 11110, and the inverse sweep in A transfers 11110 to right I. Each elementary sweep is a definitional computation for arbitrary untouched tails; the variable-length sweep is inductive. Whole cycle costs in variant order 726+44n, 652+40n, 800+48n, 734+44n. All positive. Local Lean 4.36.0-rc2 checked first, growth and positivity against copied zipper definitions; growth uses propext and Quot.sound, first propext. Repository-source never bridge accepted in run 45873034483.

Source packed in Raw391LEFourPhase.lean.xz.b64, decompressed SHA256 f6b4214ffd898eac2882a23b9555976a1d995e04a2ff7f4d0e77b3f6bdbec2da. Semantic dispatcher includes candidate proof. No complete 1LE or parent Cover yet.
