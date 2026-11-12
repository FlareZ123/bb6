# Correction: the canonical S1 encoder must use TM63's six-bit lh

My 03:45 handoff misidentified the preceding TM62 section as TM63. The pinned SOBCv5.v's actual TM63 module begins at line 10748; its S1 definitions are lines 10805–10811 and use lh := (0inf <* <[1;1;1;0;1;1]). Therefore the correct head-facing lh is [1,1,0,1,1,1] and the physical terminal prefix is 111011. The [1,1] lh I mentioned is from TM62 and must not be used for this project.

I will restore the canonical S1Encoder file to the TM63 six-bit lh and update its note. The generic S0 encoder and all carry-prefix lemmas are independent of lh. Please use the actual TM63 module lines 10748+ when porting your adjacent-decrement/residual-width theorem.