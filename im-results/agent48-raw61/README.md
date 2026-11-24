# Raw61 unary tripling

Two leaves (1344,1346) share a positive return from D with left list 00(11)^(n+1), right empty, to D with left list 00(11)^(3n+3), right empty. At the inner phase D has 5+6k zeros followed by 1+2n ones. Two transfers increment k and decrement n. Terminal transfer at n=0 gives 6(k+1) ones. The blank start reaches the outer family n=2 at step 36. This proves unbounded live prefixes by induction. Both local exact-zipper proof modules compiled under Lean 4.36.0-rc2, only propext and Quot.sound; original-source wrapper awaits full audit. Run emit_tripling.py to generate the two complete modules; these are candidates until accepted by original-source Lean. Remaining 14 leaves in candidates.json.

## Recursive unary counter

Leaves 314,315,316,319,1085: let F(n,S) be D with left 0011 (1111)^n 0 and right S; G changes only the first zero to one. For arbitrary S, F(0,S) reaches G(0,S) in 10 moves. F(n+1,S) reaches F(0, (0000)^n 0001 S), then G(0,...). A 0000 token from G(j,...) moves to F(j+1,...), and 0001 moves to G(j+1,...). Induction simultaneously on all completed smaller parameters proves F(n,S) reaches G(n,S); the terminal blank-tail transition G(n,[]) reaches F(n+1,[]) in 18 steps. Blank start at step 31 is F(1,[]). All five complete proofs of unbounded live prefixes locally compiled with exact copied zipper, standard axioms only. Full source wrappers are emitted by emit_recursive_unary.py. Nine candidate leaves remain.

## Three-residue unary growth

Leaves 401 and 481: F(r,n) is D with left 00 1^r (1111)^n and empty right. The three positive macro returns are F(4,n) -> F(5,n+1), F(5,n) -> F(2,n+2), F(2,n) -> F(4,n+1). A transfer of right token 0001 adds four ones to the left in 18 steps for arbitrary left and right tails. The terminal transfer adds four ones and restores the outer D state. Blank entry is F(2,0) at step 3. Local Lean proofs passed with propext, Quot.sound. Seven candidate leaves remain.

## Multiphase sweeps

Leaf 147: at step 179, A has empty left and right (001)^3(01)^4. For independent k,n, four macro returns transform (001)^(3+4k)(01)^(4+2n) to (001)^(7+4k)(01)^(6+2n) in 506+224k+96n steps, via suffixes 00100101 and 000010101. Leaf 380: at step 470, F has empty left and right 1^11 0001 (001)^3. Five fixed phases reduce the initial eleven ones to one, adding five 001 tokens; the terminal sweep restores eleven ones while preserving the tokens. Return cost 295+54(n+5). Both unbounded-live-prefix proofs compile locally, standard axioms only. Five candidate leaves remain (14,120,227,244,353).

## Alternating-block macro and recursive language

Leaf 120: seven-phase return from D at step 1398 with left word 0011111(01)^(19+n)10011011, right empty, to same family with n+14. Exact 1882+54n step cost. Leaf 353: define Good words by bases empty, 1, 11 and left prefixes 1111, 110, 010. F(w,R)=D with left 00w/right R; G(w,R)=D with left 10w/right R. For every Good w and n, F((1111)^(n+1)w,R) reaches some G(w',R) with Good w'. This uses recursive carry into the suffix at prefix 110, saving 001/0001 tokens to right, and restoring 010 plus repeated 1111 on return. The positive blank-tail macro G(w',[]) -> F(1111w',[]) in 18 steps closes the invariant; blank start reaches F(1111,[]) at step 26. Full local Lean unbounded-live proofs accepted with propext, Quot.sound. Remaining three candidate leaves: 14,227,244.
