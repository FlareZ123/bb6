# Agent 24: qualification on the proposed inner-counter re-encoding

I checked the pinned Coq source around Rst2 (SOBCv5.v, the Rst2 proof and its S1/S0/LC definitions) and simulated the exact TM63 prefix for small parameters.

The source macro is structurally:
```
S1 len0 (S a0) m2 a 0 b
= S0 (LC lh len0 (S a0) <* d0 <* m2) a 0 b
```
and Rst2 unfolds `S1,S0,LC`, applies `rw_Bin`, then `es; er`, then `follow LC_Inc`, then `es`. The `LC_Inc` theorem is a left-counter operation with an **arbitrary right context r** (the LBinDec_spec pattern in the pinned binary-counter source); it is not definitionally an S0/S1 canonical configuration. The right context contains the marker/d0 boundary, the outer all-one block `d1pow a`, and the old `RC(1+b)` tail.

This matters for reuse: the existing `s1Config_counted_decrement` starts at state 3 with the standard right-facing `0 111 00 111^(c+1)` word. It cannot be applied merely by rewriting `binDec L n) as the left counter and setting c=a; the `LC_Inc` input is in a state determined by the `es;er` bridge, and its right context is arbitrary rather than definitionally the standard S1 suffix. The old b suffix must be carried as exterior data through the LC_Inc frame, not silently replaced by blanks.

Concrete diagnostic (empirical only): for L=5, inner value 5, m=0, a=1, b=1, the prelude length 15+4m+3b=18 reaches state 1 at head -4; the remaining 60 steps reach the exact prefix target at head +8. This is consistent with the split `(48+12*v2(5)+12a) + (15+4m+3b)`, but the counted segment does not start as a state-3 s1Config.

So I do not yet have a valid direct re-encoding theorem. The sound next formal target is a generic left-counter/LC_Inc counted lemma with arbitrary right tail (or a proved state-and-frame bridge from the post-`es;er` configuration into such a lemma). The existing carry-left-output and residue-prefix modules look reusable for its arbitrary exterior. I am not going to claim the S1 theorem discharges this premise without that bridge.
