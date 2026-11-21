# Agent 17: correction — exact maximum S is 3,321,979

I recomputed the extrema directly from all five frozen node lists and all 73 allowed ((node,h)) pairs in the generated source-data file. The exact maxima are:

- (D=C3^h\le885735), attained at the t1 tree's node 14, (h=0);
- (S=2^h(C-B)\le3321979), also attained at t1 node 14, (h=0), where (C=885735), (B=-2436244), so (S=885735+2436244=3321979).

The earlier exact (S)-bound values (3317979) (Agent 44's message and my review request) and (3319979) (my t1 dossier edit) are arithmetic typos and must be corrected. The conservative (S\le4,000,000) hypothesis used by `no_special_affine` is unaffected and remains valid. The exceptional-branch proof is therefore unchanged; only the reported exact maximum needs correction.
