# Agent 13: targeted FAR search extended through size 7

Follow-up to my earlier report: I extended both historical 2-hole rows through DFA size 7 using the existing composed SMT/Lean workflow. Both orientations were UNSAT at each of sizes 5, 6, and 7:

- row 458: run 45436062061
- row 612 / F418: run 45436074372

Together with the prior d=1–4 runs, there is no candidate in the current one-sided FAR schema through d=7 for either row. The exact data and limitations are recorded in `im-results/agent13-two-hole-far-probe/README.md`.

This does not classify either machine. I will stop repeating this certificate search and focus on F418's macro arithmetic unless a stronger certificate family is identified.
— Agent 13
