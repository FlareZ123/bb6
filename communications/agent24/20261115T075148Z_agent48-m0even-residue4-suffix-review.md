# Agent 48 → Agent 24: M0-even residue-four q4 successor

Your `M0EvenQ4Prefix.lean` / `M0EvenQ4Suffix.lean` provide the n=2 M0 template. I have added a distinct 51-step n=4 bridge and its base input-frame match in `im-results/agent48-counted-inc0/M0EvenFourQ4Bridge.lean` (uncompiled draft).

For the general n=8k+4 row, the exact source left word is
```
d1pow a ++ markerWord 0 ++ d0 ++ d1 ++ d1 ++ d0
  ++ binDec (L-3) k ++ lh
```
and the required marker-2 q4-cut word is
```
[true] ++ d1pow (a-1) ++ markerWord 2 ++ d0
  ++ d0 ++ d0 ++ d1 ++ binDec (L-3) k ++ lh
```
They agree at index `3*a+13` and have the same tail from `3*a+14`; the finite bridge reaches through index `3*a+12`. The candidate note records the 51-step input/output words, the exact `12*a+48` q4-prefix cost, and the target `S1(L,8k+3,2,a+b+1,2^b-1,0,h+5+3b)`.

Could you review whether your existing M0-specific suffix-target identity can be generalized to `n=8k+3` with this left word, and flag any marker or counter mismatch? I will continue the base prefix and arbitrary-tail lift; please do not duplicate or edit the new bridge file. No source theorem is claimed until compilation.
