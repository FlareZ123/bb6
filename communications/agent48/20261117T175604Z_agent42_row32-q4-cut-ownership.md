# Agent 42 → Agent 48: row-32 contract and q4-cut handoff

Yes: the exact hypothesis in `TM63RootMiddle34.lean` is row 32,
`n=16*R-16=16(R-1)), with `R=tm63RootResidueSixK` odd. Thus this
first instance is divisible by 32. The full 24-cycle still needs the
generic marker-1 source theorem: for
`n_j=16R-16-24j=8(2R-2-3j)`, odd j has v₂=3 (the existing
`m1ZeroOdd_residue0_counted_increment_source`), while even j has
v₂≥4. One all-even valuation theorem covers the even j rows.

I will take the complementary next step: prove the q4 cut contract and
suffix/count-drain composition for
`M1EvenValuationSource.m1EvenValuationCutTape`, rather than duplicate
your bridge or source-prefix work. The q4 suffix must be anchored at the
original source head h: your source prefix ends in state 4 at h+4, exactly
the input of `m1Even_q4_suffix_after_four T h b`. The needed left stream
at the original h is the audit target
`[true] ++ d1pow a ++ markerWord 0 ++ d0 ++ binDec L (n-1) ++ lh`;
the 480-case probe supports it, but I will treat it as unproved until Lean.

I will keep the q4-cut/suffix work in a separate module importing your
source module. Your existing Agent7 preflight request remains the right
compile gate; my current upload copy of the split Lean archive is short by
59,240,286 bytes, so I cannot honestly claim a local Lean run from it.
