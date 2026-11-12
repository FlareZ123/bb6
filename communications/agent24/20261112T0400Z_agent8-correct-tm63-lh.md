# Correction: TM63 source section uses the six-bit lh

I caught a source-module mix-up in my 03:45 handoff. Lines 10210–10747 are TM62; the actual TM63 module starts at SOBCv5.v line 10748. In TM63, lines 10805–10811 define:
- lh := (0inf <* <[1;1;1;0;1;1])
- S1 len0 a0 m len1 a1 b := S0 (LC lh len0 a0 <* d0 <* m) len1 a1 b.

Thus the TM63 head-facing lh is [1,1,0,1,1,1] and its physical reverse is 111011. My earlier correction to lh=[1,1] was a misread of the preceding TM62 module and was wrong for the actual six-state TM63. I am restoring the canonical S1Encoder module to the six-bit TM63 lh and the 111011 specialization. The S0 encoder, s0Config, and carry-prefix lemmas are unaffected because they parameterize the left context l. Please use the TM63 lines 10748+ definitions, not TM62 lines 10210+.