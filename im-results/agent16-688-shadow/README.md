# #688: near-full-exponent shadow exclusion

The result connects to Agent3's exact collapsed arithmetic model. It uses unchanged `Inverse.lean` and its dependencies (archive SHA256 a7fdb1646cf7b0f0e42f0825558e4612f80f1802e3b99aa99ea535484ab4e574), from `im-results/agent3-688-diagonal/proof.tar.xz.b64`.

Let j be a candidate odd stopping index, k=j+1, p=2k, X=2^p-k. Define the positive shadow transitions
- H: (2u,v) -> (u,v+u+1)
- L: (u,2v) -> (u+v,v).

**Theorem (kernel checked):** if D<p, 4k+2D+7<2^(p-D), and the shadow starting at (k,k) has no path of length D+1, then OddReach X X is false. This replaces the earlier sufficient depth j-2 by 2j-O(log j).

At each inverse depth d write x+U=2^(p-d)A, y+V=2^(p-d)C, A,C>0. U+V increases by at most one per step. The high-bit gap simultaneously ensures x,y>=7 and excludes the exceptional even feeder 2x+y=8*2^t+1: the feeder power would be at least 2^(p-d), whereas the required residue 2U+V+1 is positive and strictly smaller than this modulus. Regular predecessor parity and affine equations then match the shadow. The induction does not assume that all shadows correspond to authentic paths.

`Shadow688.lean` proves the general transfer. `ShadowSource.lean` discharges the parent-law assumption using the actual Agent3 theorem `odd_large_parent` and adds `root_halt_shadow_gate` to the exact collapsed halt criterion. Compiled locally against the unchanged archive in Lean 4.36.0-rc2, all audited theorems depend only on propext, Classical.choice, Quot.sound.

## Finite experimental application

Exact integer breadth-first scan for odd j=1..9999, capped at depth 20000. A candidate with first empty depth d is excluded if d-1<p and 4k+2(d-1)+7<2^(p-d+1). All but 13 pass. Residual indices:

1,3,7,9,199,265,1189,1899,2369,3605,6529,6623,8321.

Agent3's prior exact inverse work already excludes the first seven; the remaining six are not decided here. This finite scan is ordinary computation, not a kernel-checked table. In particular j=2369 has first empty shadow depth 12417, refuting the uniform j-2 extinction conjecture (and the new threshold does not close it either). At 6529 and 8321 the depth cap is reached with nonempty shadow. An exact original-coordinate inverse search for j=1899 timed out after processing >80 million nodes; no result inferred. The unbounded family of indices remains open.

Reproduce by decoding shadow-proof.tar.xz.b64 (SHA256 990d89d4273ea39b269d40a3c6742309f4808e4de51ea60509b2561a9dbe5609), extracting alongside Agent3's files, and compiling Collapse, Phase, Root, Inverse, Shadow688, ShadowSource in that order with LEAN_PATH=. and lean -o NAME.olean NAME.lean. Compile scan.cpp with a C++17 compiler and run without arguments. The bounded scan uses only small integers: sum starts at 2k and grows by <=1 per step. No giant power is evaluated (exponent >=63 is automatically larger than the bounded correction).
