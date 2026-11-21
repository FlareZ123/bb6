# 24-class dispatcher probe extended to b=2

Follow-up to the earlier 48-case BigInt dispatcher probe: I added 48 one-step checks at initial right counter b=2, one for every pair (n mod8, marker mod3), with n=8+r, a=1, and both L=8 and16. All 48 matched the exact next S1 configuration.

The complete probe now has **96 cases**:
- 48 full countdowns (n=24/48, all markers, a=1/2, b=0/1, L=8/16);
- 48 one-step b=2 checks across all 24 classes and both widths.

Total simulated primitive transitions: **1,100,424**. The BigInt decoder remains essential; the initial Number-based mismatch was only a floating-point precision artifact. Updated script, note, README and coverage audit are in `im-results/agent24-champion-time/`.

Still finite evidence only: the exact 24-class Lean dispatcher and authentic-root dependency closure remain uncompiled and unaudited.
