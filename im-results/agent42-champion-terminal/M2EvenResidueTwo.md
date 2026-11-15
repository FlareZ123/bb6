# Marker-2 even residue-two source row: bridge reuse reduction

**Status:** exact finite-bridge reduction and deterministic replay; the new universal Lean source theorem has not yet been formalized or compiled. Keep this in `im-results/`.

## Target

Prove the original-TM2 counted increment

`m2Even_residue2_counted_increment_source
    (L q a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hbound : 8*q+2 < 2^L) (ha : 0 < a) :
  run tm2 (proposedIncrementCost 2 (8*q+2) a b)
    (s1Config L (8*q+2) 2 a 0 b h) =
  some (s1Config L (8*q+1) 1 (a+b+2) 0 (2^b-1)
    (h+5+3*b))
`

This is the 24-cycle class **(2,2)**: marker 2 and binary index n = 2 (mod 8). It is the natural successor after the current marker-1 n=8q+4 row and the already available generic marker-0 odd row n=8q+3. In the authentic root specialization, q=4k+1 when the preceding index is 32k+12.

## Exact binary boundary

With the repository's head-facing `binDec` convention, repeated `binDec_even`/`binDec_odd` gives

- source: `binDec L (8*q+2) = d1 ++ d0 ++ d1 ++ binDec (L-3) q`;
- target: `binDec L (8*q+1) = d0 ++ d1 ++ d1 ++ binDec (L-3) q`.

The marker-2 source stream is therefore

`d1pow a ++ markerWord 2 ++ d0 ++ d1 ++ d0 ++ d1
  ++ binDec (L-3) q ++ lh`

and the marker-1 target q4 left stream is

`[true] ++ d1pow a ++ markerWord 1 ++ d0 ++ d0 ++ d1 ++ d1
  ++ binDec (L-3) q ++ lh`.

## Reuse the existing 38-step bridge

The already formalized finite kernel is in
`im-results/agent48-counted-inc0/M2EvenSixQ4Prefix.lean`:

- input `⟨3,0,[-7,-6,-5,-4,-1,2]⟩`;
- output `⟨4,2,[1,-1,-4,-7,-8,-9,2]⟩`;
- exact length 38;
- all intermediate heads confined to [-9,2].

After the standard (3a+2)-cell left sweep, this window sees only the final two marker-2 cells, the following `d0` block, and the first five cells of the source `binDec` stream (plus the two swept cells at positive relative coordinates). For every q:

- source 8q+2 begins `d1 ++ d0 ++ ...`, so those five cells are `11100`;
- the existing base source 6 begins `d1 ++ d0 ++ ...`, with the same five cells.

Thus the **same exact 38-step bridge** and its existing head-confinement certificate apply. No new finite simulation is needed.

For the output boundary:

- target 8q+1 begins `d0 ++ d1 ++ ...`, so its first five cells are `00111`;
- the existing base target 5 begins `d0 ++ d1 ++ ...`, with the same five cells.

The bridge's leftmost affected coordinate is the cell at source-stream index 3a+11. From index 3a+12 onward, source and target share the exact tail

`[true] ++ d1 ++ binDec (L-3) q ++ lh`

(the last bit of the second low-order block, followed by the third block and the high-order quotient). This is the key half-line frame equality. It explains why the n=2 row can reuse the n=6 bridge even though the third low-order block differs: that block is strictly beyond the bridge's read/write window and is part of the common tail.

The remaining q4-prefix proof follows the existing M2-even-six decomposition:

1. `counted_left_sweep (3*a+2)`;
2. apply `m2EvenSixQ4Bridge_exact` through `bridgeAt`, using the five-cell boundary match above;
3. prove the target q4 stream has its first 3a+2 cells equal to one, then apply `E_scan` for 3a steps to return the head to h;
4. establish the unchanged right-facing `q4RightFacing b` shape;
5. use `q4_suffix_run_to_s1Config` to obtain the q4 reset prefix.

The q4 suffix is independent of q; its right-side shape depends only on b.

## Exact cost

Because 8q+2 = (2(4q)+1)2, v2(8q+2)=1. The q4 prefix and suffix costs are

- prefix: 44+12a;
- suffix: 39+3b.

The generic all-ones counted drain costs

`6*4^b + 42*2^b - 12*b - 48`.

Their sum is

`6*4^b + 42*2^b - 9*b + 35 + 12*a
  = proposedIncrementCost 2 (8*q+2) a b`.

The final head is `h+5+3*b`, matching the target above. The source theorem can then use the existing parity-complete `s1Config_reset_prefix_then_counted_drain` composition.

## Deterministic replay

`m2_even_residue2_replay.js` directly simulates the original six-state transition table from the exact S1 encoder and checks full finite-support tape equality at the predicted cost. It tests:

- q=0,...,4;
- the minimal valid width L≥3 and one extra width;
- a=1,2,3;
- b=0,1,2,3.

Result in this invocation: **120/120** exact endpoint matches, including state, head, and the complete set of nonblank cells. This is computational evidence only; it is not a proof for all parameters.

## Next proof action

Implement a small `M2EvenResidueTwo.lean` module by reusing the 38-step bridge declarations from `M2EvenSixQ4Prefix.lean`, not by copying or re-simulating the bridge. The essential new lemmas are:

- the two low-three-bit `binDec` expansions above;
- equality of the post-sweep bridge window with the existing n=6 input;
- equality of the source and target tails from index 3a+12;
- the full q4-prefix tape equality and counted suffix/drain composition.

Do not promote this to `results/` until the source theorem compiles and its transitive axiom audit is `sorryAx`-free.
