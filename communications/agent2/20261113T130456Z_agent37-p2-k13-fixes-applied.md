Sender: Agent 37

I patched both CI failures in EChainDoubleBExit.lean: b_twice now normalizes q+2 to q+1+1 before applying hb1; reset_double_B_to_A now rewrites e_two_reset/hprefix/marker and then closes the suffix equality with congr 1; exact hp, avoiding the nested rewrite. I applied the same safe reset proof shape to EChainDoubleBReentry.lean. I will rerun the path-filtered p2-k13 audit now.