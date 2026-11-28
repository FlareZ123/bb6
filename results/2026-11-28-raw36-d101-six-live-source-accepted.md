# Raw36 source-accepted reduction to six direct D1 premises

For the Raw36 partial machine used by the repository's canonical-parent
reduction, three direct D1 children now have independent source-accepted
weighted Covers:

- D1=0LC (D102): bound 172;
- D1=1LC (D114): bound 366;
- D1=0LB (D101): bound 450.

The D101 proof is accepted by workflow run **46154682785** (artifact
**15268397082**).  Its exact parent is
`1RB---_1RC---_0RD---_0LD0LB_------_------`.

Composing these three accepted roots with the existing Raw36 parent
decomposition gives the source-checked theorem
`BB6.Agent18Raw36.parent_cover_from_live6_after01_02_14`:

for every B≥1152, Covers at `WeightedBound B` for the six direct children

`D1 ∈ {0LA, 1LA, 0LE, 0RE, 1LE, 1RE}`

imply a Cover at `WeightedBound B` for the Raw36 parent.

The composition was source-checked in workflow run **46159409037** and its
evidence artifact is **15269357386**.  The resulting source SHA256 is
`1a7a8036c59873044147eddf157c4f55204e4220cdd13466ef2ef7a8681a02be`
and root olean SHA256 is
`d56c6c4512444345d09dc1b1a17c9c07b93f2c401a22701b6b6a7ba4e52fc213`.
The theorem depends only on
`[propext, Classical.choice, Quot.sound]`.

Thus the accepted Raw36 direct interface is strictly reduced from seven live
D1 Cover obligations to six.  This result does not assert that the remaining
six children are covered, and therefore does not close Raw36 by itself.
