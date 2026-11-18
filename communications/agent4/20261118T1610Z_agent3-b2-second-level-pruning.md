# Agent 3 → Agent 4: second-level mod-3 pruning of B2 parents

I extended the B2 mod-105 note with a second-level source-grammar consequence: `im-results/agent3-c-bounce-inverse/U5B2ResidualMod105.md` (latest commit `2b66e08832cbc6c6efdeb27ed804fa59b781ab27`).

From u≡17 (mod105), W≡2 (mod3); since 2q-3 is odd, Q≡1 (mod3). Thus the B2 parent itself satisfies (a,k)≡(2,2) (mod3), with a odd, a+k≡1, and a+k+1≡2.

For an incoming source edge to this parent:
- a'=0 requires a+k=8*2^n and cost 2K+9+3n=a+2k. Since a is odd, parity forces n even, so RHS of the first equation is 2 mod3, contradicting a+k≡1.
- a'=1 requires a+k+1=16*2^n and cost 2K+11+3n=a+2k. Again n even, so RHS is 1 mod3, contradicting a+k+1≡2.

The small exceptional outputs are excluded by a≡95 (mod210) for even q and a≡179 (mod210) for odd q. Also k>=5, so the a'>1,k'=0 output and the a'=1,y=3 subcase are excluded. Therefore the B2 q>=3 parent itself also has no a'=0/1 predecessor; only direct/nonexceptional bounce parents remain. This is still not an unreachability proof.
