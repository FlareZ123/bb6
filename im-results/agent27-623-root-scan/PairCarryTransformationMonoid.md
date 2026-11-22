# Paired-carry transformation monoid

## Result

The committed 66-state paired-carry transition system has a transformation monoid of **475 distinct maps** under the nine digit-pair input symbols.

The complete closure was computed by breadth-first enumeration from the identity transformation. For each discovered map, all nine one-symbol extensions were computed; enumeration terminated after processing all 475 maps, with every extension already represented.

| Property | Value |
|---|---:|
| Paired-carry states | 66 |
| Input symbols | 9 |
| Distinct transformations | 475 |
| Maximum shortest representative length | 6 |
| Shortest representatives by length 0–6 | 1, 9, 75, 216, 150, 18, 6 |
| Rank-1 (constant) transformations | 66 |
| Idempotent transformations | 142 |

Transformation rank distribution:

| Image size | Number of transformations |
|---:|---:|
| 1 | 66 |
| 2 | 288 |
| 3 | 42 |
| 4 | 63 |
| 5 | 6 |
| 7 | 6 |
| 8 | 3 |
| 66 | 1 |

Every one of the 66 states occurs as the image of exactly one rank-1 transformation. The shortest representative lengths of these 66 constant maps are 2 (six maps), 3 (48 maps), and 4 (12 maps). Thus the paired-carry automaton is synchronizing in the ordinary deterministic-automaton sense.

## Reproducibility

- Source transition table: [PostResetCarryPairClosure.json](../agent49-parity623/PostResetCarryPairClosure.json)
- Generator: [compute_pair_carry_monoid.js](compute_pair_carry_monoid.js)
- Full certificate: [PairCarryTransformationMonoid.json](PairCarryTransformationMonoid.json)

The certificate contains a shortest representative for each transformation, its action on all 66 states, and the 475×9 transition table of the monoid automaton. IDs are assigned by breadth-first discovery, processing symbols in numeric order 0–8.

## Relevance and limits

The 475-state monoid provides a finite summary of the action of an arbitrary suffix on every paired-carry state. It may replace explicit suffix strings in the buffered S-window product, and the 66 constant maps identify words that erase all dependence on the incoming paired-carry state.

This is a computational result relative to the committed 66-state transition table, not yet a Lean-certified theorem. It does not prove that every authentic root window contains a synchronizing word, nor does it close the source-permitted S-window transition system. The next useful step is to formalize the certificate or compose this 475-state monoid with the buffered-window transition relation.
