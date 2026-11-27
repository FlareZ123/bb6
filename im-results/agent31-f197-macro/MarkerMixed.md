# Mixed-token marker descent and generic wrapping

Use the notation of MixedCarry.md. An arbitrary aligned right tape R can carry the PPJ marker:

    B(P P J Y,R) ->^(141) B(T Y,V A τ 11 R)

where V=11000 (a two-one/three-zero run). Here 11 R means two literal ones prepended to R; Y need only start in a 1. The middle arbitrary-token scanner then acts on T Y. If T Y is W·terminal·X in the four-token grammar, let f be its initial flag and E its mixed emission word. Its result is J E X / x D_f(V A τ 11 R).

There are two exact marker decoder cases. With R=e, the decoder returns J T P A H(f) E X / e in 50+4f steps. With R=u R', it returns J J T P A H(f) E X / x R' in 55+4f steps. All six elementary source equalities are direct literal run reductions guarded by first-bit alignment.

Thus, for arbitrary mixed inner word W, PPJ Y/e returns J T P A H(f) E X/e in 238+68|W|+14t, with t counting true flags in W and its terminal. For an arbitrary mixed outer prefix U followed by token k=P or Q, the whole k PPJ Y branch becomes a uniformly composable terminal:

    B(k PPJ Y,R) -> B(J J T P A H(f) E X, x D_flag(k)(R))

at cost 279+10flag(k)+68|W|+14t. The new generic wrapping theorem (Wrap.lean) composes any uniformly aligned right-tail-parametric base of this type with arbitrary surrounding four-token prefixes, not just the AAA/TAA terminal. The full outer reset has cost 306+68(|U|+|W|)+14(t+countFlags(U)+flag(k)) and output A H(firstFlag(U,flag(k))) emit(U,flag(k)) J T P A H(f) E X. Both full reset families preserve X and increase the finite encoded prefix by exactly 2 bits by the same telescoping width argument as MixedCarry.

Local Lean 4.36.0-rc2 accepted wrap, markerUniform, descentMixed, descentBase with only propext and Quot.sound against the literal Macro source slice. The initial variable-length P-counter proof was superseded by this generic wrapping proof; no failed proof or sorry retained. This covers every known P^n PPJ mixed-suffix descent (take U=P^(n-1), k=P for n>0) and arbitrary mixed prefixes preceding k. It is not a proof that all reachable J markers satisfy the two-P pattern. Full blank-orbit closure is open.
