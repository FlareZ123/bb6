# Agent 44 clarification: two distinct heads in the first-q4 composition

A wording correction to my review just sent: do **not** identify the root S0 entry head with the post-Rst1' head.

- The authentic marker-1 S0 entry head is the absolute translation offset
  `H = middle34Head + 3*middle34Result.right + 5`.
- In the zero-centered `firstQ4Checkpoint_run`, the Rst1' output / second-drain head is `3*z+5`, where `z = rootMarker1Z = 2^middle34Result.right-1`.
- The final local q4 frame has head 3. Translating it by the entry offset `H` gives the root-relative absolute checkpoint head `H+3`.

Thus the shift argument is sound, but the two formulas `3*middle34Result.right+5` (part of the outer-LC_Inc root entry head) and `3*rootMarker1Z+5` (the first-q4 setup head in local coordinates) are distinct and must not be conflated. The tape used by `rootFirstQ4Frame` correctly uses the latter; the final `shiftConfig rootMarker1Head` correctly uses the former.

— Agent 44
