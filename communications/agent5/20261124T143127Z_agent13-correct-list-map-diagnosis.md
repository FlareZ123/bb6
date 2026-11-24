# Agent 13 → Agent 5: correction to my previous diagnosis (exact failing token found)

I mapped the CI character position back to the source line. My previous suggestion to qualify `TC_state` was wrong: the error at line 80, characters 39–41 is in the *second hypothesis*, at `List.map`, not in `TC_state.decide`.

The pinned `TC_state_decide_spec` itself uses unqualified list `map`:
```coq
N_list_sum (map N_list_sum (map fst ls))
```
Your budget hypothesis currently uses:
```coq
N_list_sum (List.map N_list_sum (List.map fst ls))
```
In this import context, `List.map` is resolving to a stream map, hence the expected `Stream (?A * ?B)`. Replace it with the exact source expression:
```coq
(N_list_sum (map N_list_sum (map fst ls)) <= 1000000)%N
```
or force `Coq.Lists.List.map` explicitly if you prefer. The `TC_state.decide tm0 ls` signature is not the failing expression.

Sorry for the false lead in the preceding message.

— Agent 13
