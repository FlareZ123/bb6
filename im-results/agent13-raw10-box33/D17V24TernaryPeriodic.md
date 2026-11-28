# D17V24 ternary carry and periodic block witnesses

Records 1, 3 and 32 of d17v24-full-residual.json share a ternary carry mechanism. At state A encode a finite least-significant-first word on the left with 00, 01, 10 for digits 0, 1, 2. Implicit blank digits are zero. The scanned-inclusive right stream at carry count zero is 011, blank, or 00b respectively, followed by blanks. At positive carry count k it is 01 followed by 2(k-1)+d zeros, then 1, then the variant tail (b for record 32, blank otherwise). Here d=2 for record 1 and 1 otherwise. Pop digit 2 in four steps and increment k; digit 0 or 1 flushes k zero digits, increments the next digit and returns to the zero-carry base. All return segments have positive length. Record 1 initializes in 17 steps; records 3 and 32 start at the base. Strong induction on a proposed halt time rules out all halts.

Box33D17V24Ternary.lean contains the exact table and original-source bridge. The core neverBlank theorem compiled locally under Lean 4.36.0-rc2 using literal copied stream definitions, reporting propext and Quot.sound only. Full original-source closure dispatched separately; do not count as accepted until CI passes.

Record 16 has a periodic block witness discovered by discoverBlock(machine,[4,1,2,2],[4,1,2,2],12000), then compress: 18/19 states and 89 tuples reduce to 11/13 states and 41 tuples. Exact data in d17v24-m16-periodic.json and generated Lean source in Box33D17V24M16.lean. Source acceptance pending.

Both witnesses are consumed by replay_direct.py. Eight exact records in the saved complement remain without these witnesses: 5,12,27,28,33,35,41,49. This does not yet close the parent or any global Cover.

## Binary packet return laws (records 35 and 49)

The shared proof in Box33D17V24BinaryPackets.lean uses A configurations with blank right stream and left words (100)^n 101 b for 35, (101)^n 1001 b for 49, where b is any finite binary suffix followed by blanks. If b=1^k 0 u, the return replaces b by 0^k 1 u and n by n+1 in exactly 12n+2k+21 or 6n+2k+19 steps respectively. Initialization occurs at 9/55 steps. The two model-level neverBlank theorems have a successful local Lean check (propext, Quot.sound); the original-source bridge audit is queued. Exact table consumers are integrated. The remaining candidate complement is now 5,12,27,28,33,41.

### Residual 27: five-cell counter

At A with blank right tape, the even phase has left `(01)^(2m) 0^6 b`, where b is a finite sequence of five-cell digits `00000` and `10000`. After exactly `16m+18` steps the odd phase is `(01)^(2m+3) 0^4 b`. For b=`(10000)^k 00000 u` (including the implicit blank digit), the odd phase returns to the even phase at m+2 with b=`(00000)^k 10000 u` after `16m+20k+54` steps. The proof uses exact sweeps with arbitrary tape tails, not bounded simulation. Blank start is even phase m=0. Local Lean model theorem checked with standard axioms; full original-source CI queued. Source: aef1d3b4d1683c797146161e572fa53955bdeeaa; replay a532c828c9957381ef64ecc40dc1ec171eabc377.

Remaining saved residual IDs: 5,12,28,33,41.

### Residual 12: packet amplification

Let P(a,b,u) denote A with blank right stream and left `(10)^a 0 (10)^b 11 u` for arbitrary stream u. A positive return P(a,b+1,u)→P(a+2,b,0u) takes exactly 6a+6(b+1)+13 steps; P(a,0,u)→A with left `(10)^(a+3)u` takes 6a+13. The reset `(10)^a 00u`→P(0,a,1u) takes 6a+8. Thus P(0,b,u), b≥2, advances to P(0,2b+3,1 0^(b−2)u), preserving the invariant. Initialization reaches P(0,4,1 blank) in 53 steps. Local Lean proof has only standard axioms. Source bridge 7ad9d6c5aec0986bc7cd44cfc0b9420d6377c2e9; replay 666a07faafd385a49ea70c47bec9fd312bef444c; full CI queued.

Remaining saved residual IDs: 5,28,33,41.

### Residual 5: recursively nested sweeps

With p=10, q=01, let S(n,u)=0011 q^n 00u, T(k,u)=q^(k+1) 000 p^k 11u. These denote left streams at A. A complete epoch at right 001z carries S(n,u) to S(n+1,11 q^n 1u). The key transfer is A(T(k,u),001r)→A(u,1^(2k+4)0 1^(2k+5)r), for arbitrary u,r. Its strong-induction proof uses a chain of strictly smaller nested transfers, with right balanced runs and a decreasing zero-pair counter. The restore lemma reconstructs T from two odd unary runs; a separate even/odd finish restores S. Initialization reaches S(0,011z) at 71 steps. The local Lean neverBlank theorem uses only standard axioms. Source cb8f29eb070967fb97ec4996b564b98695ffa539; replay 1b335e08624c7c8597a3a065d613d26c3d2f6f61; full CI queued.

Remaining saved residual IDs: 28,33,41.
