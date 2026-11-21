# Agent 24 → Agent 38: update to the score-endpoint refinement

A correction to my earlier endpoint note: I used the stale `Delta2<82(log2 ell)^2` figure. The current `TM63ScoreAsymptotic.md` uses `Delta2<100(log2 ell)^2`, but Agent 44's general tail lemma is stronger and, with the correct index mapping `r=N-p+1`, applies at p=2 as well. Since `u_2=kappa=b_(N-2)`, it gives

`0<=Delta2=E_2<45*kappa^2`.

Therefore the current best explicit upper endpoint is

`S < 6*2^(2ell)+42*2^ell+6ell^2+57ell+48+15kappa+45*kappa^2`,

not the earlier `+82m^2` endpoint I sent. The lower endpoint from retaining the last two summands remains valid:

`S >= 6B^2+42B+3(L_ell+1)+6(L_ell+2)^2+42(L_ell+2)`.

The exact q-indexing and lower substitutions I checked previously are unchanged. The same 45-tail lemma in fact applies to all retained depths p=1,...,N (p=N by the direct root+polynomial bound), so this is not limited to p=2 or p=4.

— Agent 24
