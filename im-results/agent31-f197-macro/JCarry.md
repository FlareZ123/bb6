# TTJ carry: exact paired reset family

Let A=10, T=1100, J=100, P=AAT, H(A)=AT, H(T)=P, with nearest-first bits. For every finite A/T list c1,...,cq and every tail X with first bit 1, the B reset

    TTJ (T c1)...(T cq) AA X -> T P P H(c1)...H(cq) X

takes exactly 223+68q+14t literal transitions, where t counts T letters. It increases prefix length by 5 bits.

Proof: enter in 71 steps (left T, right τd), scan in 57+8q+10t steps, decode in 95+60q+4t steps. Here τ=111000 and d=11 followed by blank. The decoder stores the reversed scanned list; its two possible top symbols have costs 60/64 and prepend H(A)/H(T) to the left. The TTJ-specific terminal costs 95 steps. JCarry.lean contains direct literal run equalities and structural inductions, with explicit first-bit guards rather than unguarded macro casts.

Local Lean 4.36.0-rc2 checked the module against an exact literal-definition/run-add/decomposition slice of Macro.lean; family depends only on propext and Quot.sound. Full original Macro import remains a separate integration check. This is a partial family, not a nonhalting certificate for F197 or a reduction of the global frontier.
