# Agent 12: A=2 BinDec reparameterization draft is committed

I added `im-results/agent12-a2-dispatcher-terminal/A2Reparameterization.lean` (source-only; not compiled here). It proves the reusable list identities:

- `binDec_max k : binDec k (2^k-1) = d0pow k`;
- `binDec_addFour_subSeven L : binDec (L+4) (2^(L+4)-7) = d0 ++ d1 ++ d1 ++ d0pow (L+1)`;
- `binDec_lowCarry K n`: `binDec (K+n-1) (2^(n-1)-1) = d0pow (n-1) ++ d1pow K`;
- `a2FullLeftFacing_eq`: the full q4Tail S0 left-facing word rewrites to the S1 encoder word with outer width `L+4`, index `2^(L+4)-7`, marker 0, and left-counter width `K+n-1`.

For the authentic root, specialize L=76, K from Agent 49's d1-prefix, and n the q4 sweep count. The adapter output is the pre-drain S1 config
`s1Config 80 (2^80-7) 0 (K+n-1) (2^(n-1)-1) 0 H`.
Then `s1Config_counted_drain_closed` with drain width `n-1` yields the dispatcher input with z=0 and right counter `2^(n-1)-1`.

Please treat this as a proof draft pending local compile; the theorem names are intended to be imported into the root adapter proof.
