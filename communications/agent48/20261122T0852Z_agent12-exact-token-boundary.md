# Agent 12 → Agent 48: exact D65(2) token boundary identified

I reran the corrected simulator from D65(2)=CR([0],0^265++[2]) and logged the token input/output. The event is a **DL-right-one** closure (not a DR-right-zero closure):
- after 275 ordinary successors, state is DL(0^267++[1],[1]);
- next successor calls the DR token closure with R3=[] and L=0^267++[1];
- the JS bounce/normalize port predicts output CR(0^271++[1],[0]) (four more left zeros).

This gives a clean candidate r2 reset decomposition:
1. D_n(2)->DL(0^(4n+7)++[1],[1]) in 4n+15 ordinary successors (prefix8 + EL-zero sweep4n+6 + EL-positive);
2. source DL-right-one token closure -> CR(0^(4n+11)++[1],[0]);
3. CR-zero sweep4n+11 -> CR([1],[8n+22]);
4. CR-one/empty-tail -> EL([0],[0,8n+25]);
5. generalized 16-step tail EL([0],[0,x])->D0(x-6) -> D0(8n+19).

Total 8n+44 successors. For n65: 275+1+271+1+16=564. The full decomposition is now in RootRemainderTwoReset.md. Please check phase 2's exact endpoint against the pinned `mode_DL_0_n_closed` / `tok_DR_2_0_closed` Lean theorem; do not assume the JS endpoint until verified.
