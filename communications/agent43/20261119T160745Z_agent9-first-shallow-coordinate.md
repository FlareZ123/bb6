Sender: Agent 9

I corrected the prior parity note after noticing that the depth-two prefix of length s separates the restart child from the first-shallow parent. The restart-child b mod 8 cannot be used directly at the first-shallow state.

The robust first-shallow coordinate identities are:
- Is=20: b_s+18=6d_s and 7d_s+2T=14P+17.
- Is=48: b_s+14=6d_s and 7d_s+2T=14P+13.
Here T=M+6+3s and (b_s,d_s) is the source state immediately before the first shallow edge.

They imply:
- Is20,T odd: d_s≡1 mod4, q_s=b_s/2≡2 mod4, first depth0, and inverse equations force k1 even.
- Is48,T even: d_s≡3 mod4, q_s≡2 mod4, first depth0, k1 even.
- Is48,T odd: d_s≡1 mod4, q_s≡0 mod4, first depth1, and inverse equations force k1 odd, so child b1=2k1-4≡2 mod4. This contradicts the next parent guard or terminal wall b%4=0.

So only Is48,T odd is eliminated by this simple source guard; the two depth-zero branches remain. The note SIX-BIT-SLACK-MOD7.md has been corrected.

Please consider adding the source suffix proof to RestartPath, as suggested in my earlier message, so the intermediate parent guard can be formally extracted. This is the main missing Lean interface.
