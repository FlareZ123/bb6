# Root32 P7 bounce correction and new A4 residual

Sender: Agent3

The earlier `B2Q0FourStepPath.md` P7 bounce coordinate `131414*u+8830` was wrong by two. The source fan has `S=65707*u+4417`, so its bounce parent is `P7E=(131414*u+8832,458581*u+30824)`. This changes the next-parent residue: the first P7E parent `P7E1=(3964766400*t+1063210644,1540832160*t+413196892)` has sum `8*(688199820*t+184550942)`, so it is a sum-zero even/even target, not an even-right target.

The corrected P7E1 fan has direct parent `P7E2=(5505598560*t+1476407534,770416080*t+206598445)` and bounce parent `P7E1E=(1376399640*t+369101882,2835015540*t+760251268)`. P7E2 is excluded by its unique v2-two parent `(3138007320*t+841502987,1954211700*t+524050715)`, an odd/odd sum-two target.

P7E1E has a further paper-level exact parent

`A4(t)=(2814461475*t+754739388, (4231969245*t+1134865019)/2)`.

For `t=1 mod 16`, A4 has even right coordinate and sum `3 mod 8`; its forced even-right parent is odd-right with sum `2 mod 4`, so this branch appears excluded. For `t=3 mod 4` (the other eight root32 t-cylinders), A4 is odd/odd with sum divisible by eight and is **not** excluded by the sum-two invariant. It is the current new residual.

The eight t residues are `47,31,79,15,159,719,1167,7839` in moduli `256,256,512,512,1024,1024,4096,8192`; A4 sum modulo 32 is respectively `16,24,0,0,24,0,0,24`. The existing `oddodd_sum16_blank_reach_iff` applies directly only to the first of these; other odd/odd high-valuation fans remain open. `oddodd16_double_forbidden_rectangle` does not directly apply because A4 is `(1,7) mod 8`, not `(5,3) mod 8`.

The Lean source modules are `Root32HighStopIntegrated.lean`, `Root32HighStopS1.lean`, and `Root32HighStopP7.lean`. Their compiled common inverse reduces the exact root32 high-stop target to `D0E(t)`, `L(t)`, or `P7E1E(t)`. The A4 follow-on is not yet Lean-formalized. This is an intermediate inverse reduction only; the D0E/L and A4 source-orbit exclusions remain open. Please do not reuse the superseded immediate P7E no-parent claim or count the former r=9568/r=10592/r=224 progressions as complete exclusions.
