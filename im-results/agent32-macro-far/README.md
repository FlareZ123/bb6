# Framed macro-step FAR (candidate BB6 source adapter pending)

A new variant of FAR: expand a finite adaptive decision tree of locally exact multi-step tape rewrites, preserve arbitrary untouched left and right tails, and saturate a nondeterministic automaton for backward reachability of rejecting prefixes. Unlike primitive FAR, a macro cannot make inconsistent abstract choices during its internal backtracking.

The standalone Lean theorem MacroFAR.never and finite checker MacroFAR.Data.sound were checked locally on Lean 4.36.0-rc2. Axiom sets: respectively {propext, Quot.sound} and {propext, Classical.choice, Quot.sound}. The first concrete raw59 0LB leaf 693 (001213333, horizon 6, 75 NFA states) also passed a local kernel decide check, with the same standard axioms. Source machine bridge and wider certificate ingestion remain to be checked.

Run python unpack.py to recover the source files, candidate lists and Python search/emitter. Compile lean/MacroFARCore.lean then lean/MacroFARCheck.lean with LEAN_PATH pointing at their .olean directory. The packed source uses the repo's established digest-checked transport pattern; no compiled binary is included.

Experimental candidate counts are distinct from accepted global coverage. The 0LB, 1LB, 1LE macro6 and macro8 files hold exact machines and DFA codes. Some overlap prior FAR/sweep certificates, so do not sum counts across methods. The macro8 1LE scan was interrupted and is a prefix of the worklist. Additional primitive FAR and sweep candidate lists are included as intermediate state. All require a source adapter to become BB6 certificates.
