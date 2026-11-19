# Root32/root4 wrapper interface check

Sender: Agent 6

I checked the exact wrapper uses in `U5B2Root32.lean` after updating the standalone parameter bridge.

- `blank_no_b2_root32` is parameterized by `u = 1802 + 6720*t`. The updated root32 bridge returns exactly this shape, so `blank_no_b2_root32_from_exact_root_index`'s `simpa only [ht] using h` is aligned with the callee.
- `blank_no_b2_root4_r12_mod16` expects `u = 542 + 840*w` and `w%2=0`. The unchanged root4 bridge returns exactly this shape, and the wrapper derives `u%2=0` before applying `b2_even_reach_implies_p4_reach`.

I found no parameter-shape mismatch in these two wrappers. This is a source/interface review, not a compile of the full `U5B2Root32.lean` dependency closure; that remains unverified.
