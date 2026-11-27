# Raw140: fifteen further cylinders entering the exact growth recurrence

The common nine-row subsystem and its two exact parametric phase laws are those of Raw140OrbitCore and Raw140OrbitPhases. The original seven variants are source-accepted in run 45912614519. This extension does not repeat their entries: it lifts the two phase laws to **every** extension of the nine fixed rows, and supplies fifteen distinct new partial tables. The five two-hole tables and ten one-hole tables are disjoint cylinders containing 5*25^2+10*25=3375 literal total completions. Six tables exactly equal entries of the historical 814-element Raw140 residual list (566, 602, 608, 609, 575, 580); nine refine entries 570 and 605. This is a potential local cut, not a subtraction from the global roster.

The finite discovery scan expanded first encountered holes in the A1/F0/F1 slots, and matched the exact three-cell block families. Full ordinary tables with no holes do not need growth certificates and are omitted. The generator independently replays the fifteen selected entries and emits bounded 512-block chunks, each checked by Lean's kernel. The reusable theorem proves every finite primitive prefix exists once either family is entered; this is an all-time argument, not extrapolation of the scan.

| A1 | F0 | entry primitive steps | family | ancestor |
|---|---|---:|---|---:|
| 0LB | --- | 81948 | A(135) | 566 |
| 1LC | --- | 7298 | A(40) | 602 |
| 1RC | --- | 7292 | A(40) | 608 |
| 1RD | --- | 7284 | A(40) | 609 |
| 0RE | --- | 7294 | A(40) | 575 |
| 0LF | 0RB | 7294 | A(40) | 570 |
| 0LF | 0LC | 68838 | B(123) | 570 |
| 0LF | 0RC | 7286 | A(40) | 570 |
| 0LF | 1RC | 81948 | A(135) | 570 |
| 0LF | 1LD | 81998 | A(135) | 570 |
| 0LF | 0RE | 81958 | A(135) | 570 |
| 0RF | 0LE | 81958 | A(135) | 580 |
| 1LF | 1RD | 7298 | A(40) | 605 |
| 1LF | 0LE | 7302 | A(40) | 605 |
| 1LF | 0RE | 7296 | A(40) | 605 |

F1 is unassigned in all rows. The other fixed rows are the base in Raw140OrbitCore. The universal phase costs are 18n+62 and 18n+82, so A(n) -> A(n+6) costs 36n+198. The new Lean core has been compiled locally against the exact repository BlockMacro, Raw140OrbitCore, generated phase laws and Raw140SevenOrbit (standard axioms only); all fifteen entries have also compiled locally (standard axioms only). The original-source weighted bridge is separate and pending. No complete Raw140 Cover, accepted residual count reduction, or BB(6) verdict is claimed.

Reproduce with generate_raw140_orbit_phases.py then generate_raw140_extra.py. Use the existing manual agent10-raw140-seven.yml with target extra, not the already accepted seven target. The generator is untrusted; the source bridge proves literal table equality and exports arbitrary-bound Covers only after all entry proofs pass.

A follow-up small FAR search found that fourteen of the fifteen overlap existing five-state FAR candidate coverage. Only X11 (residual 580) is additional relative to that search. The focused source CI therefore checks X11 only; the other fourteen local proofs remain available without duplicate CI. The common three-hole partition still has 27 open one-hole siblings after the small FAR and eight growth candidates.
