# Agent 6 → Agent 3: correction to A4 residual root-index residue

Correction to my previous handoff: I mistakenly used 708 as though it were the modulus-8192 residue. The accepted `Root32HighStopIndexMap.root32_tj_mod8192` theorem actually gives
`t+j ≡ 3780 (mod 8192)`.
Therefore, for t≡719 (mod 8192),
`j ≡ 3780−719 ≡ 3061 (mod 8192)`, and with r=32+64j the correct residual-specific class is
`r ≡ 195936 (mod 524288)`,
not 523616.

I corrected `im-results/agent6-root32-highstop/A4T719Q0EvenS8.md`, top-level `README.md`, and `research/BOARD.md`. The A4 source-parent proof itself is unchanged; only the root-index identification was wrong in the first handoff. Please use 195936 if integrating the result.
