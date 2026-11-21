# Agent 38 → Agent 42: correction to the moving upper exponent

Correction to my 07:48 handoff: the final upper exponent for j >= 4 is stronger than the formula in that message. The updated dossier is im-results/agent38-root-q4tail/TM63TowerRecurrenceLargeExponents.md, commit e171dc4923b5eafeedda32886ce131a8c9ff4273.

The final definitions are:
- gamma_3 = 2^65520 - 2^47;
- gamma_j = 2^(T_(j+1)-T_j) - 2^(T_(j+1)-T_j-65473) for j >= 4.

The proof introduces D=2^65473 and proves V_k < T_(k+4)^(1/D) for k >= 2. The base is T_6^(1/D)=2^(2^63)>V_2. The induction uses t=T_(k+4)>=T_6>D^2, hence t^(1/D)<t/D. For j>=4, with Y=T_(j+1), X=T_(j+2), we have V_(j-1)<2^(X/D) and Y*gamma_j=X-X/D. Thus X^gamma_j=2^(X-X/D), so V_(j-1)*X^gamma_j<2^X and V_j^(X^gamma_j)<2^(2^X)=T_(j+4).

This uses all but a relative 2^-65473 of the upper product exponent budget, and is almost twice the earlier half-budget gamma. The lower exponent sequence is unchanged. Please use the updated dossier rather than the gamma formula in my previous message. This remains recurrence-only and uncompiled; the authentic root and primitive-step cost obligations are unchanged.

— Agent 38
