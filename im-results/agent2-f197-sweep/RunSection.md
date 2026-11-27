# Run-level section and an exact obstruction to unconditional product invariants

This supplements README.md. The following are mathematical reductions, not a decision of F197.

## Run representation
At D, write L=0 X with X a nonempty run word of ones followed by internal gaps 1 or 2 (terminal gap e means infinite zeros). At B, L=X, shortened right R=0W, where W is a nonempty run word beginning 1. A symbol (a,g) denotes a ones followed by g zeros, g=e terminal. Put A=(1,1), J=(1,2), T=(2,2), E=(1,e). Left D prefix changes in run notation:
D01 pushes A, D111 pushes J, D1000 pushes T, D1011 pushes AA, D110 increments old top run and pushes A, D1010 pushes A and reverses, D00 reverses without changing X.

These operations and the parametric B blocks in README imply the following exact return map even when the right grammar G fails. Write W as a run word, inc(W)=increment first run (or E for blank), and (a,g)W as prepend. At B with nonblank X and even top a:
- terminal: next nonblank B left E, right W'=(1,a-1)W;
- g=2: next B left A followed by remaining runs, same W';
- g=1: next B left incremented first remaining run, same W'.
This includes the forced D00 after B0 (leading a+1 zeros).

For odd a:
- terminal: combine B/F/A, blank B0, D01, D00; next nonblank B left AE, right (1,a)W.
- g=2: A1 returns D with remaining runs and right (1,a+2)W, leading zero count z=0.
- g=1, next run (b,h): if h=2, B loop returns with both runs consumed and W'=(b+1,a+2)W; if h=1, A1 returns D with both consumed, right (b+1,a+2)W, z=0; if h=e, combine blank B0 and D01, return D with left AE and right (b,a+2)W, z=0.

At D write right as z leading zeros followed by run word Y. Blank reverses to B with W=E. For z>=2, reverse to B with W=inc(Y) if z=2, otherwise (1,z-2)Y. For z=1 consume 01, push A. For z=0:
- first a>=3: consume 111, push J; if run exhausted expose its gap;
- a=2: consume 110, increment L top and push A, expose gap g-1 or blank;
- a=1,g=e or g>=3: consume 1000, push T, expose gap g-3 or blank;
- a=1,g=2: literal fatal prefix 1001;
- a=1,g=1 and next run b>=2: consume 1011, push AA, shorten or remove next run;
- a=1,g=1 and next b=1: consume 1010, push A and reverse; if second run terminal W=E, if second gap=1 W=inc(remaining), else W=(1,second gap-1)remaining.

Thus right gaps need not be assumed odd in a direct decision algorithm. If left runs are capped at K (overflow a BAD target, not an assumption), internal right gaps and exposed zero counts are at most K+2. Right run lengths can be represented soundly by exact 1..R and large classes modulo 3: inc exact; subtract 1,2,3 either stays large or crosses threshold, include both possibilities. A one-stack-exact pushdown solver can keep finite right prefix plus suffix language, with two or three run contexts shown insufficient in experiments (spurious fatal / unsafe B).

## Finite product obstruction at ALL B episodes (including blank left)
Take B stacks in bit convention of README, with shortened right r=0W. Start after 9 live steps at (11,01). Let T be one exact B episode (the j/k block), followed if it exits to D by a complete D scan to the next B. Suppose an invariant at all B episodes is a product X x Y, contains (11,01), and is T-closed with no fatal. The following finite derivation contradicts that. Each row's two input components separately occur in the seed or earlier rows' outputs; hence product closure forces membership even if the pair itself is not on the literal orbit.

| input L | input r | output L | output r |
|---|---|---|---|
| 11 | 01 | 1 | 0101 |
| 1 | 01 | 0 | 010001 |
| 0 | 01 | 101 | 01 |
| 11 | 010001 | 1 | 01010001 |
| 101 | 01010001 | 0 | 0110001010001 |
| 0 | 0110001010001 | 101100101 | 01001 |
| 101 | 01001 | 0 | 0110001001 |
| 0 | 0110001001 | fatal D prefix 1001 | L=01100101 |

Here 0 denotes blank left. Last row B0, D01, D1000 reaches fatal. This is an exact finite obstruction to the entire product-invariant class, not a literal blank-orbit halt. The table is independently reproducible by product-obstruction.cjs.

**Important distinction:** grouping blank-left excursions into a single nonblank B return changes the class. A separate exact finite projection-closure experiment (1,000,001 combinations, 8,646 distinct left words, 17,821 distinct right words at cutoff, word length <=60) found neither a fatal nor a forbidden B run in that grouped class. No proof: the closure is not exhausted and the length cutoff discards words. This suggests investigating regular product languages at *nonblank* B only, rather than treating every B boundary identically. Do not cite the finite obstruction as ruling out this grouped class.
