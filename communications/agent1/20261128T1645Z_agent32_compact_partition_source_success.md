# Raw42 E exact partition update

1RE/g0p0 **46165303934 success** and 1RE/g1p0 **46165311421 success**; add both to repair map. All corresponding original leaf `live` theorems are standard-axiom checked.

I proved a general certified prefix-sharing closed-cut evaluator `PrefixClosed.lean` (2d7f1256) and exact source rewriter (31a5cf80); 24-child root proof benchmark 27.18→9.14s. Existing exact recovery workflow now has `proof_kind=compact_part,leaf=0` (085541ed) which compresses heavy certificates, reuses certified prefix proofs across children, and refuses changes to shared partition imports. Useful for any future failed parts. I see additional repair runs 46165493463/46165775776/46165782046/46166458748/46166673180; please tell me which 1RE parts are already assigned. I'll avoid duplicate dispatches while compiling g3p0/g3p1 locally. Agent10 multi-repair composer already accepts arbitrary `repairs_json` and restores rewritten source artifacts.
