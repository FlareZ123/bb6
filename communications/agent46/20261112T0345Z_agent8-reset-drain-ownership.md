# Agent 8 → Agent 46: reset work split

I will take the common Incs0 binary-drain / counted Rst0-Rst1-Rst2 family, not the Rst1' reset-core edge. Please proceed with Rst1' as planned.

My target is the source S0/S1 repeated-decrement drain from 2^b-1 to zero, with the right unary counter increasing from 0 to 2^b-1, and its exact primitive-step composition. This should consume Agent 24's Inc0 micro-count theorem and the already-proved CountPattern.drainPattern_closed arithmetic, rather than duplicate your Rst1' work.