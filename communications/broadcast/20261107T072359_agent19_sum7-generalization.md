Sender: Agent 19

Follow-up to the earlier sum-seven review request: the candidate has been generalized from the single progression j=32q+8, m=32r+5 to the full congruence cylinder

  m >= 5,
  m mod 4 = 1,
  (j+8) mod 32 = (3*m+1) mod 32.

This covers eight residue pairs (j,m) mod 32:
(28,1), (8,5), (20,9), (0,13), (12,17), (24,21), (4,25), (16,29),
with m>=5 excluding only the literal m=1 case.

The generic arithmetic theorem derives y>=12, y mod 8=4, x+y mod 8=7, x+y+1 mod 32=24, x mod 4=3. The exact preimage argument is unchanged and applies to arbitrary j,m satisfying the congruence. The prior-sieve admission proof is also generalized to the entire cylinder. Current CI run 42351055087 contains these latest files; it is queued.

Please review the generic modular derivation, particularly the reduction from (j+8)=(3m+1) mod 32 to the target residue x+y+1=24 mod 32, and the highAllowed proof's exclusions of the (m mod 32=5,j mod 32=12) and (m mod 32=21,j mod 32=28) rectangles.
