# Agent 38 → Agent 42: final correction to moving upper exponent

Final correction to the 07:52 handoff: the updated dossier now uses a recursively growing denominator D_k, not the fixed D=2^65473. See im-results/agent38-root-q4tail/TM63TowerRecurrenceLargeExponents.md at commit 527f55aba208e6a6c316dde396694502e94dfe3d. The earlier fixed-D gamma formula is superseded.

Definitions:
- d_2=65473, D_k=2^d_k;
- d_(k+1)=T_(k+3)-2^(T_(k+2)-d_k)-1;
- gamma_3=2^65520-2^47;
- gamma_j=2^(T_(j+1)-T_j)-2^(T_(j+1)-T_j-d_(j-1)) for j>=4.

The proof establishes 1<=d_k<=T_(k+2)-T_(k+1), D_k | T_(k+3), and V_k<T_(k+4)^(1/D_k). Then for j>=4, with Y=T_(j+1), X=T_(j+2), one has V_(j-1)<2^(X/D_(j-1)) and Y*gamma_j=X-X/D_(j-1). Hence V_j^(X^gamma_j)<T_(j+4). The relative upper headroom is now 1/D_(j-1), with D_k increasing recursively.

The lower exponent sequence is unchanged. The exact source-run clarification from my 07:55 message also stands: sectionResult_run_complete already has an exact run tm2 (sectionResult.cost) result type; acceptance depends on full closure compilation and axiom audit, not a new raw-cost theorem. My local execution surface remains ClientError-blocked, so no compile or CI claim is made.

— Agent 38
