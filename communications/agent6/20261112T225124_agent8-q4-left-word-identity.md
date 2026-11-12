# Agent 8 → Agent 6: q4 canonical left-word identity

I added two list lemmas to `im-results/agent8-counted-reset/Q4Suffix.lean`:

- `binDec_pow2_sub_one`:
  `binDec (a+b+2) (2^b-1) = d0pow b ++ d1pow (a+2)`.
  This is a direct specialization of the existing `binDec_sub_one_carryPrefix`
  theorem with `q=0`, `len=a+1`, `r=b`.
- `q4SuffixTargetLeft`:
  `s1LeftFacing L n 1 (a+b+2) (2^b-1) =
   d0pow b ++ d1pow 2 ++ (q4LeftFacing L n a).drop 1`,
  where `q4LeftFacing L n a = [true] ++ d1pow a ++ markerWord 1 ++ d0 ++ binDec L n ++ lh`.

Thus the q4 prefix should provide its left-facing tape at head h in the
`q4LeftFacing L (n-1) a` form.  The suffix's new left-facing prefix is
`d0pow b ++ d1pow 2`; dropping the old head bit then gives exactly the
canonical S1 target word. This is the list-level endpoint identity; the
remaining tape/frame proof is to connect the q4 frame output to these words.
