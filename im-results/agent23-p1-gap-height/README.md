# No-short-gap height: a new exact cylinder search and counterexample

Agent 23, 2026-11-26. This concerns the auxiliary modular no-short recurrence, not a P1 blank-orbit decision. The all-integer exponential-height question remains open.

## New concrete obstruction

For the recurrence in [Agent50's defect identity](../agent50-p1-dyadic-width/selected_gap_defect_identity.md) and [Agent43's height scan](../agent43-p1-high-cost-reset-count/NoShortGapWordResidues.md), take

    C0 = 241147905, b0 = -1
    gaps = [11,8,6,4,5,3,4,8,7,6]
    G = 62, C_final = 241147967, b_final = 3797497.

Every gap is at least three, every update b'=(C+b)/2^g is integral, and the terminal C+b=244945464 is divisible by eight. The exact integer inequality C0^20 < 2^(9G) disproves the candidate bound C0 >= 2^(0.45 G), suggested only empirically by the previous G<=57 scan. It does NOT disprove a lower exponential bound with a smaller exponent or a multiplicative constant, nor imply an actual P1 history of the target length at the critical reset.

[GapHeight.lean](GapHeight.lean) was locally compiled using Lean 4.36.0-rc2. The concrete recurrence, span and inequality theorems have no axioms; the four general algebraic lifting theorems depend only on propext, Classical.choice, Quot.sound. No native_decide or source substitution.

## Exact parameter-cylinder recursion

For an extendable prefix of span G, let S=sum 2^s over selected starts, r the least residue of C0 modulo 2^(G+3), and b the carry at C0=r. Write U=2^G. Its parameter cylinder is

    C0=r+8Uh, C=r+G+8Uh, carry=b+8Sh.

At the root G=0, S=0, r=1, b=-1, exactly encoding 8|(C0-1). Thereafter S is odd. A child gap g>=3 with M=2^g=8V exists and is extendable iff

    M | (r+G+b)/8 + V(r+G+g) + (U+S)h.

Indeed, eliminating the quotient from M*b'=C+carry and 8|(C+g+b') gives 8M | C+carry+M(C+g). Substitute the cylinder, divide by eight, and remove the term M*U*h. The coefficient U+S is odd (also at the root), so there is exactly one solution h=h0 mod M, where

    h0 = -[(r+G+b)/8 + V(r+G+g)]*(U+S)^(-1) mod M.

Then r'=r+8Uh0, G'=G+g, S'=S+U and b'=(r+G+b+8(U+S)h0)/M. Substituting h=h0+Mu proves the same affine representation at the child. These identities are the checked cylinder_step, linear_residue and cylinder_child lemmas. The inverse coefficient depends on the parent, not g, so one modular inverse serves all candidate gaps.

This allows **range-first exact enumeration**: reject a whole cylinder when its least admissible C0 exceeds X; when its modulus exceeds X-r, at most one integer remains, and ordinary exact DFS replaces symbolic recursion. Every terminal-extendable word has all earlier prefixes extendable because its next gap is >=3. Thus the tree covers every word in the selected integer range; it is not a greedy path. If b<=C/7 and C>0, then b'<=C/7<=(C+g)/7 for g>=3. This holds from the signed seed too, so g is bounded by log2(2(X+cap+64)) before the finite cutoff. The executable uses unsigned modular Newton inversion, with error squaring; an odd starting a already has a*a=1 mod8, so five updates suffice mod2^64. Only modular operations wrap; the represented clock/carry and chosen residue are bounded by the explicit X<2^58 guard.

## New finite exploration

Build: g++ -O3 -std=c++17 gap_height.cpp -o gap_height
Run: ./gap_height 72057594037927936 180

The exact integer program finished in 40.20 seconds locally:

    X=72057594037927936 cap=180 symbolic=262271568 concrete=456994468 capHits=0 maxG=117

Here X=2^56. The emitted minima over this finite seed range include:

| G | Least C0 |
|---:|---:|
| 58 | 3378820273 |
| 60 | 1237899009 |
| 62 | 241147905 |
| 84 | 772390565089 |
| 90 | 15408976527537 |
| 107 | 532674470925313 |
| 117 | 16913773385341153 |

The last witness is [3,8,4,6,4,5,3,5,6,4,8,3,7,4,3,8,7,4,4,5,8,4,4]. The minimum observed log2(C0)/G is approximately 0.449118436 at G=62. All printed witnesses were independently replayed with arbitrary-precision Python integers; for X=2^16 a direct per-parameter DFS agreed on every minimum. The range sweep is a C++ computational result, not a kernel certificate of absence for all seeds. The small explicit counterexample, in contrast, is independently kernel checked. No new workflow.

The search provides a much larger finite picture (G=117 vs the earlier G=57 exhaustive word sweep) without enumerating all gap words up to that span. It cannot justify extrapolation of any positive exponent. The next mathematical question remains whether a universal bound C0 >= c*lambda^G holds for some lambda>1, or there exists a subexponential-height family. A solution must cover arbitrary switching, not just terminal 3-runs.
