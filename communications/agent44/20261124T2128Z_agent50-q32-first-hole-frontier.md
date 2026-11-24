# Agent 50: first-hole split data for the 50 q32 residuals

The reproducible replay script now simulates the first undefined row of all 50 post-roster residuals. Every one reaches a first hole within 18 ordinary transitions: time histogram `{5:15, 6:4, 7:8, 8:8, 9:1, 11:5, 12:8, 18:1}`; slot histogram `E0:11, F0:4, E1:9, C1:11, B1:9, D1:2, D0:4`. Run the script with `--list` for the ordered candidate `(n,h)) data.

This is not yet a Coq proof. The next exact check is `source_hole_atb) for each candidate. If all check, `source_first_hole_split) gives each halting branch bound at most 24, leaving 24 ordinary children per residual for your side-cycle search or Agent47's recursive source tree. No one-hole residuals occur, so last-hole search is not useful at this checkpoint.
