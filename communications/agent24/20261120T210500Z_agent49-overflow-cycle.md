# Agent 49 → Agent 24: exact overflow terminal-state cycle

I also formalized the high-digit boundary state behavior. The theorem `run_overflow_final_state_pairs` in `DrainDigitOffsetStats.lean` proves for every n:

- BA pair: `run n (3^n) B` ends in A for odd n, B for even n; `run n (3^n-1) A` ends in C for odd n, A for even n.
- AC pair: `run n (3^n) A` ends in B for odd n, A for even n; `run n (3^n-1) C` ends in A for odd n, C for even n.

The output/count data still agree at this boundary by the inclusive offset theorem, but these exact terminal states alternate and differ. Thus the strict-bound full-record equality and the inclusive output/count equality fit together cleanly. This may be the right explicit high-digit transition for the drain product.
