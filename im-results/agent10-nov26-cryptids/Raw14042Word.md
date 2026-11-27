# Arbitrary-word C-counter and mixed B-bank depletion

The exact C-counter proof is now independent of the previous homogeneous/triplet restriction. On the common nine-row partial table, for every word W in {2,3}*, arbitrary left context X and C-tail s, define F(X,W,s)=ER(27X,3Ws). Lean 4.36.0-rc2 accepts:

    ER(2X,3Ws) -> BL(X,22W(322)^carry(s)next(s))
    F(3X,W,s) -> F(X,2W(322)^carry(s),next(s))
    F(3^k X,W,s) -> F(X,2^k W(322)^C_k(s),turn_k(s))
    F(2,W,s) -> BL([],2222W(322)^C_2(s)turn_2(s))

The proof is induction on W. The old forwardOne handles 2, and BL6 returns 2. For 3, ER(2X,33Y)->ER(22X,3Y) in 7 steps; BL(2X,22Y)->BL(X,223Y) in 15 steps. The central prep rotates the tail. Thus arbitrary arrangements of 2 and 3 preserve their word order. All four primary theorems report [propext, Quot.sound].

Also checked: Raw14042BMixedEnd.emptyEven, for arbitrary Y,

    ER(1,1^a5 2^(b+2)Y) -> BR(5,22 1^(a+1)23 2^bY).

The empty-left boundary is handled by the original left_zero/right_zero lemmas and the framed 32-step end0 bridge. This has the same axiom report.

Generate Raw14042WordLocal.lean and Raw14042BMixedEndLocal.lean with the associated Python generators, respectively. Both generators use the earlier generate_raw140_42_mixed.py finite block certificate emitter. Compile dependencies in the existing Raw14042Counter closure. No source-table extension is needed; no F1 read occurs in any of these laws.

The odd A mixed depletion is separately checked in Raw14042MixedOdd.lean (commit 63f36c6). These are local reductions; no full blank-orbit closure is asserted.

Application to B62542 with p even: let a=p/2, b=a+1, and (n,s) be the C-tail rotation from rank 3 through (p-4)/2 rounds. The checked mixed B iteration followed by emptyEven gives BR(5,22 1^(a+1)23 2^(a-1)(322)^n s). Paper-level subsequent bridge: CR(6^5 4,5 1^(a-1)23 2^(a-1)(322)^n s), and each two ones increase the left exponent by four. For a odd this yields AR(3^(2a+6)2,2^a(322)^n s), hence C(4a+4,n,s). For a even, it gives AR(3^(2a+3)2,023 2^(a-1)(322)^n s), then the common counter with a nonhomogeneous 2/3 word. Its scan is covered by the new arbitrary-word theorem. The paper-level bridges still need formal composition, and the depleted nonhomogeneous word needs reduction to a standard section.
