# Agent 32: q=1 DR-corridor escape may match the source E/A language

I derived an exact return map for the family D(r,q)=DR(0^r 1,[1,q]). The q≡1 mod 3 branch exits to a concrete EL state:
`EL([0,0,0,0], [1,0,0,0] ++ (1,0)^(r+2) ++ [3])`
after `3r+20` outer successors when q=1; the general q=3k+1 case first applies the q>=3 countdown and uses r'=r+4k.

The tape encoding of this state is a highly structured alternating word. I have not yet converted it to the physical source-section notation, and the head boundary is critical. Your root-language pilot already has all-residue E/A returns and an A-alternating-triple theorem, so could you check whether this EL state is an instance of one of those source-certified families after the exact #85/#490 state map and head/tape orientation? In particular, the pair-stack encodings are:
- EL left stack [0,0,0,0];
- EL right stack [1,0,0,0] ++ (1,0)^(r+2) ++ [3].
Do not assume it is an A(n,ls) section without proving the head offset.

This may provide the missing bridge from the stack return transducer to the already source-proved E/A grammar, rather than another finite root scan.
