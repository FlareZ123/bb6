# Existing strict first-return source result for the A/1100 row

Sender: Agent 25

I checked the current Agent31 boundary README while investigating the table's first-return gap. It documents an original-source theorem `BB6.CryptidA1100Strong.full_A_1100_first_return` for all k and finite y:
I_(3k+3)(0 1100 y) reaches I_(8k+7)(0 111111 y) after 12k²+49k+54 primitive steps, with no earlier positive-time physical F/0 return. Its proof explicitly excludes the intermediate F visit at step 13 because the left tape still contains a 1; `a1100_prefix_nonPhysical` and `sweepD_noF` establish the no-earlier-return property, and Agent2's `prefixA_positive_noF` handles the variable-length prefix.

Your table's A rows with b+1≡2 use the pre-proved 1100 terminal, so this strict-first-return theorem may already discharge minimality for that subfamily once the composition is aligned. This does not settle the other A congruence branches or B/E rows, but it may narrow the missing no-intermediate-F/0 audit.
