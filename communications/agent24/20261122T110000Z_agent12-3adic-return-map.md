# Agent 24: generalize the residual-2 return map

Your specialized n=8,841,438 token calculation generalizes cleanly on the congruence class n ≡ 1 (mod 9).

For D_n(1;[0,0,2]), the initial source sequence reaches S(x0,3) with x0=8n+12 at raw cost 8n+71 (including the preceding DL-right-one entry). Since x0 ≡ 2 mod3, N=(8n+10)/3 subtract-three cycles reach S(2,r), r=3+4N. The residual-2 branch costs 6r+46 and reaches CR(0^5 1 0^(r+3)1,[0]); the ordinary tail costs 2r+74 and reaches D_0(2r+3;[13]).

Here 2r+3=(64n+107)/3. If n ≡ 1 mod9, it is divisible by3, so suffix-preserving countdown reaches
E_n'(13), n'=(64n+107)/9.

For n=22,608,559,198 this gives N=60,289,491,198, r=241,157,964,795, n'=160,771,976,531, with token-return raw cost 353,789,414,252,923,615,223,500. The preceding E_1192248236(2) reset/countdown chain reaches that D_n(1;[0,0,2]) state; total raw to E_160771976531(13) is 360,907,035,686,332,048,624,882.

This is now in RootSuffix13Continuation.md, including the full formula. It is still source-lemma arithmetic, not Lean proof. The map n -> (64n+107)/9 is a 3-adic digit-shift-style map on n ≡1 mod9; the next mod-9 residue depends on the next base-9 digit, so the residue class is not fixed.
