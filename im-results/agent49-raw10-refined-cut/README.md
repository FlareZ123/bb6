# Raw10 refined residual: inclusion consumer (33 / conditional 31 boxes)

## Mathematical interface and evidence

A source-indexed closed rectangle continues to bound every refined subrectangle, even when extra certified cylinders fragment it. For finite complete slot enumeration S, if each allowed set of r is included in the corresponding allowed set of c, then Fits r m implies Fits c m. RectCover.lean proves this and the generic explicit-complement consumer in Lean 4.36.0-rc2 (local compiler b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a). Both exported theorem axiom profiles are exactly [propext, Quot.sound].

The exact Raw10 adapter Raw10RefinedCut.lean uses the existing source remainder constructor, the same 65 side witnesses, held leaf, fixed cycle and two-move halt cylinders as the expanded 41-box interface, and source box bounds for 8 and 18–24. It deliberately has no dependency on the old canonical77/78 roster or legacy generated import chain. Its source build is **not yet accepted**. The held-leaf premise remains explicit so the adapter does not silently rely on a separate proof route. The 16/17 bounds remain explicit premises.

Independent executable combinatorics (replay.cjs, run from any directory with Node.js) on the actual 66 encoded source rows gives:

| Original rectangle | Refined index (zero-based) | Mass |
|---|---:|---:|
| 8 | 15 | 575 |
| 16 | 23 | 3,515,625 |
| 17 | 24 | 146,250 |
| 18–24 | 25–31 | 52,500 |

The seven 18–24 boxes and the remainder of original box8 remove 53,075 completions from the 41-box partition, leaving 33 explicit boxes. Supplying original-source bounds 7376 for box16 and 7014 for box17 would remove another 3,661,875 completions, leaving 31 boxes and 90,737,499,998,775 completions. The source-level counts are candidate Lean declarations until their source closure accepts; the independent arithmetic is finite computation, not a new parent Cover or a global roster reduction.

## Remaining gates

- Compile Raw10RefinedCut.lean with the existing box18–24 generated archive and source closure; it imports only RectCover, Raw10BoxCore, Box18to24Source, Box8Closure and Raw10FixedLeaves. No standalone workflow was created. Local Lean works; direct GitHub clone fails with DNS resolution, so only the self-contained generic proof was compiled locally.
- Agent13's run 45756644007 failed at Box17SourceCore.lean:27 (rewrite direction in sourceDomainEq), after the direct box17 proof compiled. It does not establish a source bound for 17 or 16. The proposed fix is the forward rewrite of the source equality h instead of its inverse, followed by literal-domain/index and decoder equalities; this also applies to the analogous Box16 proof. Agent13 owns those source integrations.
- Once both bounds are accepted, instantiate parentCover31 and connect the held proof, then pursue remaining actual boxes, including the existing full box5 candidate. Neither parentCover33 nor parentCover31 closes the parent without every retained box's bound. BB(6) remains open.
