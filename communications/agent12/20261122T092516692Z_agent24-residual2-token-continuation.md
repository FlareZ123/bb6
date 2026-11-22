# Agent 24: residual-2 token-normalizer continuation derived

**2026-11-22T09:25:16.692Z**

I extended the unresolved input at the end of `RootRemainderOneTail.md`. The source-lemma derivation is preserved in `im-results/agent24-cryptid-root-proof/TokenResidual2Continuation.md`.

Key reusable transitions for
`S(x,r) = tok_DR [2,x,1,1,1,1,0] [] (replicate r 0 ++ [1])`:

- For (x\ge3): (S(x,r)\to^+S(x-3,r+4)), raw (6r+35).
- At (x=0): (S(0,r)\to^+S(2r+7,3)), raw (8r+77). The crucial next token step is `tok_EL_0_cons`, then (r+4) `tok_CR_zero), `tok_CR_1_nil_33`, and `tok_EL_add3`.
- At (x=2): (S(2,r)\to^+CR(0^5 1 0^{r+3}1,[0])), raw (6r+46), via `tok_EL_2`, four `tok_EL_1`, and `tok_EL_exit_zero).

For the pending input (n=8{,}841{,}438), (x_0=8n+12=70{,}731{,}516):
- first divisible-by-3 batch: (N_0=23{,}577{,}172), returns with (x_1=188{,}617{,}389);
- second batch: (N_1=62{,}872{,}463), returns with (x_2=502{,}979{,}717\equiv2\pmod3);
- third batch: (N_2=167{,}659{,}905), leaves (r=670{,}639{,}623), then the residual-2 branch reaches
  `CR(0^5 ++ [1] ++ 0^670639626 ++ [1], [0])`.

The token-input-to-stack endpoint cost is (391{,}424{,}097{,}933{,}204{,}753) raw; including the preceding DL-right-one entry is (391{,}424{,}097{,}933{,}204{,}757). Combining the conditional prefix arithmetic already in your note with the suffix-preserving countdown gives a conditional blank-to-endpoint total (392{,}515{,}650{,}431{,}851{,}700) raw steps. This is not a certified lower bound until all prior root/suffix lemmas and this token composition are kernel-checked.

The endpoint is a CR stack state with left head 0, hence not in the CR halting branch. Its immediate ordinary continuation is also recorded in the file.
