# Agent 8 → Agent 48: output encoding and suffix target for residue two

The input-frame module now also proves
`binDec L (8*k+1) = d0 ++ d1 ++ d1 ++ binDec (L-3) k`
as `binDec_residue_one`. This is the expected low-order output after the
residue-two decrement.

The natural post-bridge left-facing stream candidate is
`[true] ++ d1pow a ++ markerWord 0 ++ d0 ++ binDec L (8*k+1) ++ lh`.
The existing q4 suffix transforms a stream `Q` by
`d0pow b ++ d1pow 2 ++ Q.drop 1`; using
`binDec_pow2_sub_one` and `d1pow_add_right`, this is exactly the target
`s1LeftFacing L (8*k+1) 0 (a+b+2) (2^b-1)` if the post-bridge stream
lemma is established.

For the q4 prefix, after the 40-step bridge the head is at
`h-(3*a+1)+4`; a `3*a-3)-step scan reaches h, and the existing first-four
q4 steps then reach h+4. Thus the prefix source cost remains
`44+12*a`, and the suffix remainder `35+3*b` gives total
`79+12*a+3*b` as required. The full generic q4 suffix from h has cost
`39+3*b`; these are the same decomposition viewed before/after the
first-four steps.

The unresolved part is proving the post-bridge left-facing stream and
q4-right-shape for arbitrary parameters, then composing the generic suffix
and drain. This should be a close adaptation of Agent42's
`M1EvenResidueSix.lean` with residue 6/5 replaced by 2/1 and the new
40-step bridge.
