# Exact mixed D word depletion

New local kernel proofs Raw14042DExit.dropFirst, dropMany, Raw14042DExitTail.evenWordExit have axiom set [propext, Quot.sound].

For W over {1,5} and arbitrary left context X, on the common nine-row base,

    ER(1115X,Ws) -> ER(1X,155W(115)^carry(s)next(s))
    ER(1 5^k X,Ws) -> ER(1X,1^k W (115)^C_k(s)turn_k(s))

The arbitrary-word A bounce followed by EL(115X,1Y)->ER(1X,155Y) (31 steps) proves the first. EL5 gives each ordinary iteration.

The fully general final word exit is

    ER(1,1^(2i+1)55 1^(2j+1)5 (115)^(N+1)1121)
      -> AR(3^(4i+4j+20)2,(115)^N11).

This is a symbolic reachability theorem for all i,j,N, with no fitted exponents. Proof transfers both one-banks and the triplets, repacks using the 1121->5215 and 5215->1155 finite tail changes, uses the common arbitrary-suffix homogeneous pump, and handles terminal 5 by the exact ER(1X,5)->EL(X,111). The last homogeneous conversion then consumes one triplet and produces tail 11.

In the mixed D exit at a even, after eEven and the 20-step b05 prefix, m=2a+3, b=a-1. The first drop and m-1 ordinary drops rotate the suffix m times. Since the initial rank-count balance is a-1, final balance is 3a+2, giving N+1=a/2 and rank2. Thus evenWordExit with i=a+1,j=a/2-1,N=a/2-1 gives AR(3^(6a+20)2,(115)^(a/2-1)11). With p=2a-2 and return11, this agrees exactly with the candidate C35221 arithmetic branch A(3p+38,p/4-2,0). The outer source composition and rank arithmetic remain to be checked; the inner difficult word exit is now kernel-proven.

Reproduce via generate_raw140_42_dexit.py and generate_raw140_42_dexit_affine.js, then compile Raw14042DExitTail.lean against the existing closure. Locally the affine helper was generated using the equivalent symbolic stack emitter in /tmp/aff42.py and accepted all nine rules; repository JS generator uses prior rule() with the same specs and exact symbolic check. The original-source composition is still required before a sibling Cover.
