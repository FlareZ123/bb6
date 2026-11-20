# Agent 37: further packet-tail resets in the external 107-step chain

The packet decomposition continues beyond call 30. Writing (P(q,p;Y)=(01)^q0,1^pY), the following exact suffix decompositions are read directly from the replayed A_step2 outputs:

| Call | Input packet | Output packet | Output suffix |
|---:|---|---|---|
| 31 | (P(0,2;T_7)) | (P(2,0;U_6)) | `01010010111` |
| 32 | (P(2,0;U_6)) | (P(0,10;V_5)) | `0111111111110111` |
| 42 | (P(0,1;V_5)) | (P(0,6;W_5)) | `01111110101` |
| 47 | (P(2,0;W_5)) | (P(0,9;X_4)) | `01111111111101` |
| 54 | (P(3,0;X_4)) | (P(0,8;Y_9)) | `011111111011111111` |

where
- (T_7=1010111) (from call 24),
- (U_6=010111),
- (V_5=10111),
- (W_5=10101),
- (X_4=1101),
- (Y_9=011111111).

Between these reset points, the ordinary packet updates continue: B decrements q and preserves p,Y; E with p≥3 increments q by 2 and decrements p by 3. Thus the 107-call trace appears to be a finite packet-tail transducer with a small set of E-boundary reset operations, not an arbitrary suffix walk.

The reset map is the unresolved part: e.g. call 31 is an E,p=2 reset with a non-(F_7) tail; call 32 is then E,p=0; call 42 is E,p=1; call 47 is E,p=0. Existing fixed-tail P2 source lemmas do not by themselves establish these general tail transformations. A useful next target is a source theorem parameterized by the finite tail Y, or a compact classification of these E boundary maps. The full replay and earlier packet trace are in `im-results/agent37-echain/Astep2BoundaryReplay.mjs` and `Astep2PacketExitTrace.md`.

These are computational suffix decompositions, not yet Lean source theorems; do not treat the inferred packet parameters as a proof of a general reset rule.
