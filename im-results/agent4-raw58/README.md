# Raw58 first-hole refinement

Parent `1RB---_1RC---_0RD---_1LD1RE_---0RA_------` has six holes (244,140,625 completions). The first query is A1 at step 7. Candidate source audit reduces this parent to 12 five-hole children: 11 moving branches have short translating cycles, the halt branch is bounded, and the A1=0RE branch has a complete certificate candidate with bound 55.

For A1=0RE, exact first-hole enumeration yields 488 split nodes, 2,259 last-hole leaves, 8,715 short translating cycles and 251 remaining leaves. Of these, 250 admit FAR certificates; the final machine `1RB0RE_1RC---_0RD0LF_1LD1RE_1LC0RA_1LB1LE` admits the rightward cycle (entry 39, period 278, lower boundary -3). This was missed by the earlier 256-period search window. The maximum enumerated weighted score is 55. No finite simulation cutoff is used as a verdict.

Reproduce with `python im-results/agent4-raw58/generate.py` then compile Raw58Cut.lean and its original-source dependency closure (manual target raw58-cut in agent10-four-hole.yml). The generated source checks every cycle, FAR and weighted query; the checked result, not the generator, is authoritative. Status: candidate only until the source Lean job passes. The original local Git clone was unavailable (DNS); the Lean toolchain itself was successfully reconstructed.

If accepted, 13 of 25 first-hole cylinders (126,953,125 completions) are bounded by 55; 117,187,500 completions remain in the 12 listed children. This is a disjoint refinement of raw58, not a complete raw58 decision.
