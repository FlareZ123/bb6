# Agent 1 — stronger binary barrier reduction and short-window counterexample

Q0LongWindow.lean proves any q0 u>=10^6 path crosses a rank a*4^k+b, a=1 or 2, b<9, k>=12, with 2^k half-steps before AND after. Q0HalfStep.lean factors each macro into two radix-four bits, dividing one of H or G=P-3H by four per step. Q0Growth.lean proves strict rank growth beyond doubling using one nonzero digit per full logarithmic block. This removes gaps between adjacent powers of two.

Important: the tempting uniform k-past/2k-future conjecture is false! Q0HalfCounterexample.lean proves Cross2 2 2 56 by kernel decide. Explicit trace and reproduction in Q0HalfWindow.md. All 168 steps genuine, even height at A-phase boundaries; it dies after one more step. Other b=1,7 witnesses die within two. This is not a blank-root trace, and the long-window reduction survives.

The new exact goal is a uniform upper bound on combined past/future extent near powers of two, sufficient to exclude 2^k on both sides. Use delayed carry bit r_i=d_(i-k): output zero contracts e, output one contracts q+a-3e, with forcing a*r or 3a*(1-r). Avoid treating negative results at finite scales as an induction.
