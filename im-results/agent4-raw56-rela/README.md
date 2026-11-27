# Raw56 E1=1RE / E0=0LA — complete candidate cut

Exact partial table: `1RB---_1RC---_0RD---_1LD1LE_0LA1RE_------`.

**Status:** candidate complete; not an accepted Lean Cover. JS exact-tape enumeration gives 1,193 splits, 18,536 translated cycles, 7,336 final-hole leaves, and 1,568 open leaves. Maximum query 209, maximum cycle end 448. FAR through five states covers 1,501; 56 RLE automata plus eleven explicit unbounded growth proofs cover the remainder. No unresolved leaf in this candidate enumeration. Weight target 7014. Table-keyed parameters are in spec.json. The original C++ classifier and kernel must independently accept the cut before any global reduction. 

## Zipper notation and proof method

`A(l,r)` is a head-relative state A with left word l including the scanned cell and right word r beginning immediately to its right, both written nearest-first. Empty words denote blank continuation. Other state letters analogous. Juxtaposition is list concatenation; a superscript is repetition. Each macro below is a literal finite transition calculation for arbitrary untouched tails L,R. The macros never inspect either variable tail (except when the tail is explicitly the empty word). Thus induction on block multiplicity gives exact runs, not an extrapolation from simulations. Every section returns in strictly positive time; the blank entry and compatible completion transport are those of SweepPumping.lean. The separate symbolic verifier checks all finite identities without substituting concrete sample tails.

Use blocks W=1111, P=1010, Q=0101 unless redefined. 

### Nine related F0-hole leaves (117,121,124,1263–1265,1325–1327)

All tables are `1RB{a}_1RC{b}_0RD1RA_1LD1LE_0LA1RE_---{f}`, with (a,f) equal to (0LF,1LA), (1LF,0LA), or (1LF,0RD); b in {0LC,0RE,1RB}. The blank entry at step 11 is G(0), where G(n)=A(W^(n+1),0).

In first mode, left macro A(W L,R) -> A(L,P R) in 4 steps. In second and third modes, A(W L,R) -> A(L,Q R) in 4 and 8 steps respectively. All modes have right macro A(0 L,P R) -> A(0 W L,R) in r=6 for b=0LC or 0RE, r=4 for b=1RB.

First mode: A([],P R) -> A(0 W,R) in r; A(0 L,0) -> A(W L,0) in 11. The left sweep of n+1 blocks, initial macro, right sweep of n blocks, final macro yields G(n+1), cost (4+r)(n+1)+11.

Second and third modes: A([],010 R) -> A(0111,R) in 3; A(0 L,10) -> A(11111 L,0) in f=14 for b=0LC/0RE, f=12 for b=1RB. The word identity Q^(n+1)0 = 010 P^n 10 holds by induction on n. Thus left sweep, initial macro, right sweep n, final macro yields A(11111 W^n 111,0)=G(n+1), cost l(n+1)+3+rn+f, l=4 or 8. No F0 query occurs.

### Leaf 1305: B1 hole

`1RB1LF_1RC---_0RD0RB_1LD1LE_0LA1RE_0RF0RD`. Same G(n), blank entry 11. Exact macros:
- A(W L,R) -> A(L,Q R), 8.
- A([],01 R) -> C(111,R), 2.
- C(11 L,Q R) -> C(11 Q L,R), 4.
- C(11 L,010) -> A(101 L,0111), 9.
- A(P L,0 R) -> A(L,0 W R), 8.
- A(1011,0 R) -> E(1,W R), 7.
- E(1 L,W R) -> E(1 W L,R), 4.
- E(1 L,111) -> A(W L,0), 5.

After the left sweep of n+1 W, apply initial 2 steps using Q^(n+1)0=01 Q^n 010, then C-sweep n and turn 9. The result is A(101 Q^n 1,0111)=A(P^n 1011,0111). Sweep n P blocks, giving A(1011,0 W^n 111). The seven-step macro produces E(1,W^(n+1)111), sweep n+1 W, and final five steps give G(n+1). Total cost 24n+35. No B1 query.

### Leaf 1142: F1 hole

`1RB1LC_1RC0RF_0RD0RA_1LD1LE_0LA1RE_1RD---`. Redefine W=1011, U=1110. G(n)=A(U W^(n+1),0), blank entry 53. Exact macros:
- A(U L,R) -> A(L,Q R), 10.
- A(W L,R) -> A(L,Q R), 10.
- A([],010 R) -> A(0011,R), 3.
- A(0011 L,P R) -> A(0011 W L,R), 16.
- A(0011 L,10) -> A(W L,011), 6.
- A(0011 L,1011) -> A(U W L,0), 8.

Sweep U and n+1 W into Q^(n+2)0. Apply the 3-step initial macro, using Q^(n+2)0=010 P^(n+1)10. Sweep n+1 P right, turn in 6, reaching A(W^(n+2),011). Sweep n+2 W left, reaching A([],Q^(n+2)011). Now Q^(n+2)011=010 P^(n+1)1011. Apply initial macro, sweep n+1 P right, and turn in 8: A(U W^(n+2),0)=G(n+1). Total 52n+92. No F1 query.

## Integration

All eleven leaves have exact mathematical inductive proofs of nonhalting; the fixed transitions and blank entries are verified by symbolic_macros.js. The original Lean proof port is still required to accept these growth leaves as .proven certificates; no claim is made that a JS run establishes the full original source Cover. RLE parameters were discovered using discovery.js in the sibling directory. The local shell remains unavailable (ClientError), so a Lean compilation has not been performed. 
