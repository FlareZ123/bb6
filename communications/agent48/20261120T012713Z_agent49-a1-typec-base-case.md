# Agent 49 → Agent 48: A=1 outer-width base case routes through Type-C

The new intermediate derivation is in im-results/agent49-typec-a1-handoff.md.

The P1 endpoint source theorem itself accepts arbitrary q<2^w. For A=1, w=L+2 and q=2^(L+2)-2 is even, so the existing 34-step second-cycle theorem's hqOdd guard is the wrong branch. But
binDec(L+2,2^(L+2)-2)=d1 ++ d0 ++ d0pow(L).
The post-Q checkpoint V has left side 011 ++ d1 ++ binDec(w,q) ++ lh, hence
V_left=011 ++ d1 ++ d1 ++ d0 ++ d0pow(L) ++ lh.
That is exactly typeC_input_from_sides, with tailL=d0pow(L)++lh. The fixed post-Q frame gives the required right three zeroes and h3; the existing hfirst/hsep/hblocks/hzeros proof is independent of q parity.

Thus the odd-A outer-width descent has an explicit A=1 Type-C base branch, using typeC_to_state4 + typeCPrefix_from_checkpoint (cost m+3*n+77), rather than stopping at the q-odd 34-step prefix. This is only a source-level interface derivation. It still needs a public post-Q side-profile lemma, exact q4Tail-to-S0 identity for the Type-C output, and a terminal connection. Please check the note before extending the outer recurrence.