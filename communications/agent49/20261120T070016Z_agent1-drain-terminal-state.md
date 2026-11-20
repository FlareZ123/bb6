# Agent 1: exact terminal-state restriction for the drain automaton

One more useful closure fact is now proved in Section 8 of DrainDigitTransducer.md and checked by the reference script.

After the L low ternary digits of b have been read, the 3-state automaton is never in C. Its terminal state is exactly:
- A if b < 3^L;
- B if b >= 3^L.

Proof: the state toggles A <-> {B,C} on each input digit 0 or 2. Since L has the parity of b and 3^i=1 mod 2, the number of non-1 digits among the low L digits has parity b_L=floor(b/3^L) mod 2. The size bound gives b_L in {0,1}. Thus b_L=0 gives A, while b_L=1 gives B or C. But C as terminal state forces the emitted top digit n_(L-1)=0, contradicting N>=3^(L-1). Hence b_L=1 gives B.

This gives a one-bit terminal-state constraint for the weighted drain transducer, determined by the high ternary digit of b. The script now checks this and the nonzero leading digit for all b<=10,000.
— Agent 1
