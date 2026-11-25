# Three raw139 F0=0RC one-hole cylinders

The source table has fixed rows `1RB? 1RC? 1LD0RF 1RA0LE 0LD1RC 0RC0RE`; set A1 to any of `1LD, 0LE, 1RE`, leaving B1 unassigned. Each cylinder has 25 literal completions, all of which are addressed by the same invariant.

In the head-relative zipper with the scanned cell included at the beginning of the left word, put P=0111, Q=1001, O=111, Z=100. A word W consists of O/Z digits ending in O. The two configurations at F are
- A(m,W): left 0 P^m W P, right empty;
- B(m,W): left 0 P^m 0 Z W P, right empty.

The entry into A(2,OZO) occurs after 191, 197, 203 ordinary transitions respectively. Write d=4,6,8 respectively, and m=n+2. The four macro edges (all with positive exact cost) are:

| Input | Output | Cost |
|---|---|---|
| A(m,O^k Z T) | A(m+1,Z^k O T) | 2d+28n+12k+62 |
| A(m,O^(k+1)) | B(m,Z^k O) | d+14m+12(k+1)+20 |
| B(m,O^k Z T) | B(m+1,Z^k O T) | 2d+28m+12k+34 |
| B(m,O^(k+1)) | A(m+1,O Z^(k+1) O) | 2d+28n+12(k+1)+96 |

The partition into a first zero with a nonempty remaining word, or an all-one word, is exhaustive by induction over W. The primitive sweeps are exact for arbitrary suffix lists and arbitrary repeat counts, not finite sampling. The four edges preserve the invariant; positive costs give arbitrarily long live prefixes from the blank root. No transition at B1 occurs in these partial runs. Therefore any compatible completion runs forever.

[Champion0RCTriple.lean](Champion0RCTriple.lean) formalizes the four macro edges, invariant closure and blank entry. The complete zipper proof passed Lean 4.36.0-rc2 against a local preflight with the same move0/step0/run0, sweep and table definitions; printed axioms were only propext, Classical.choice, Quot.sound. The original-import adapter `never` and `cover_zeroRC` passed the manual `rc-triple` audit [run 45551060221](https://github.com/FlareZ123/bb6/actions/runs/45551060221), checked head b841cc49f28e44cd02b0724e058eb93cb68d8d76, with all eight named theorem axiom sets restricted to the standard three. These 75 literal completions are source-certified; integration into the complete 0RC parent is separate. This is neither closure of the complete 0RC branch nor proof of raw139 or maximality.
