# Late blank-frontier splice bank

Exact one- and two-pump certificates for the residuals from the compressed 0LA frontier recipes. Each row is an authentic blank replay, exact base epoch, equality of chronological edge-crossing lists at each cut, and a normalized symbolic word identity for all pump exponents, using the [crossing-splice lemma](../agent42-raw40-crossing-splice/README.md). The independent [finite premises checker](check_late_splice_bank.js) passes all ten rows. `side: R` mirrors spatial coordinates before recording cuts; shift is always in physical coordinates. These are mathematical certificates awaiting source-level Lean acceptance, not a global decrement.

| Child/leaf | Entry | Head | Epoch | Shift | Cuts (oriented) | Increment |
|---|---:|---:|---:|---:|---|---:|
| 0LE/366 | 729 | -15 | 494 | -6 | [[3,15]] | 112 |
| 0RE/759 | 1243 | -15 | 1466 | -8 | [[3,23]] | 544 |
| 0RE/792 | 1129 | -15 | 1312 | -8 | [[3,23]] | 480 |
| 0RE/1730 | 20104 | 80 | 48572 | 60 | [[9,229]] | 28800 |
| 0RE/1736 | 19128 | 80 | 46006 | 60 | [[9,229]] | 27200 |
| 0RE/790 | 2198 | -48 | 444 | -8 | [[15,17],[30,36]] | 30 |
| 1RE/390 | 23992 | -132 | 19302 | -50 | [[2,42],[133,143]] | 5600 |
| 1RE/1179 | 23992 | -132 | 19302 | -50 | [[2,42],[133,143]] | 5600 |
| 0RE/627 | 135300 | 1004 | 19958 | 96 | [[9,33],[688,760]] | 912 |
| 0RE/1403 | 133274 | 1004 | 19728 | 96 | [[9,33],[688,760]] | 912 |

The exact parametric epoch cost is `period + increment*n`. The normalized word identity equates the pumped final tape with the next member of the pumped entry family, including the physical head displacement. The same proof applies to every completion of the missing transition. Discovery sources: [one pump](late_splice_search.js), [two pumps](late_splice_multi.js). The sole still-unresolved residual in the five compressed frontier recipes is 1RE/1096. The two-pump discovery matches both insertions at a common pair of frontiers and uses the actual edge crossings, not just apparent growth.
