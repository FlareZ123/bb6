# Mixed right-counter closure for Raw140 sibling 42

**Locally kernel-checked on Lean 4.36.0-rc2:** the arbitrary-word mixed pair, its iteration and even-length depletion are now exact theorems on the original common partial table. The literal machine and earlier left/right/C bank context are in [Raw14042Counter.md](Raw14042Counter.md). This is a reusable source-level subroutine, not yet a complete blank-root Cover.

Write (P(m,X,W,s)=ER(27X,3,2^m46Ws)), (m\ge1), (W\in\{4,6\}^*), (s) in the six right-tail cycle (62,64,6221,6421,6405,62542), and (c(s)=1) exactly at the last suffix. Then

```
P(m,33X,W,s) -> P(m+1,X,4 W (644)^c(s),rho(s)).
P(m,3^(2k) X,W,s) -> P(m+k,X,4^k W (644)^C_k(s),rho^k(s)).
P(m,2,W,s) -> BL([],2^(m+3)46 4 W (644)^c(s) rho(s)).
```

The proof composes two exact scans. After scanning m twos (cost 19m), the marker 46 enters CR(4526Z,Ws) for Z=6^m7X. Apply Raw140Double.bounce to W and s, then the finite path DL(5526Z,Y)->BL(Z,2544Y). Sweeping the m sixes yields BL(7X,2^(m+1)544 W (644)^c rho). The previously checked finishStep removes one 3 behind 7. The second marker 54 transforms ER(2Z,354Y)->BL(Z,2246Y). The same two-scan and finishStep remove the second 3 and increment m. With X=2, use finishZero and one extra BL6 instead, giving the depletion rule. No A1/F0/F1 row is read in these laws. The formal results quantify arbitrary untouched block stacks, not finite sampled words.

Rebuild the local module with `python generate_raw140_42_mixed.py > Raw14042MixedLocal.lean`, then compile Raw14042Mixed.lean against the original dependency closure recovered from artifact 15220415544. Local kernel outputs for pair, pairs, depleteEven are all [propext, Quot.sound]. Local SHA256: generated module 7d94ffb1c9fcd081d38e39a553b5d2313a6bdd65dd02e386ff0a51edcad548bb; mixed module 6f74db529b01b9253a500e6f4452d2c30f7b87ac17261ddf8b17bc46503c56aa.

## Consequences and remaining work

For the sibling's mixed seed AR(3^p2,5215), p even, the previous symbolic seedMixed gives P(3,3^(p-8)2,44,6405). Apply (p-8)/2 pairs and one depletion. Put j=(p-8)/2 and (c,s)=(floor((j+5)/6),(j+5) mod 6). The output is BL([],2^(j+6)46 4^(j+3)(644)^c s). This exact large-bank shape replaces a previously open mixed counter. The seed and subsequent conversions must still be source-composed.

The subsequent standard-bank route has a candidate closed arithmetic formula from this shape:
- if p=2 mod 4: BR(5^(2p+6),(644)^c s);
- if p=0 mod 4: BR(5^(3p+20),(644)^(p/4-1)64).
The derivation uses the common initTwos/twoPump, a24ToD, dIter, eIter, an extra 466 marker path, and eOddLast. It is currently paper-level with finite regression tests; it is not included in the checked exports above.

At the authentic earlier paper-level root p=12472 this predicts BR(5^37436,(644)^3117 64), then 1700 right-bank returns to BR(5^57836,6421), then A0(57844). The arithmetic drain is z=6n+rank(s); each bank return changes z to z-11 and increases p by 12. Thus the drain has k=max(0,floor((z-1)/11)) iterations.

The next significant open cases in an arithmetic orbit model include B-bank terminal 62542 and odd mixed A5215. No all-time invariant or certified blank-root decision yet.