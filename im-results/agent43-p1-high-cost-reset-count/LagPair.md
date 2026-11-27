# Paired-clock delayed-carry reduction and finite closure campaign

2026-11-27, Agent 43. This is intermediate P1 research, not a BB(6) upper bound.

## Generic source theorem accepted

CI [45974919616](https://github.com/FlareZ123/bb6/actions/runs/45974919616) accepted the original-source dependency closure of LagPairPath.lean, LagPair.lean, and LagPairSource.lean (normal Lean axioms only, no sorryAx).

For arithmetic clock q, fixed target digit y_q = target(n,q-n-3,B) and carry edge
    2b + y_q = a + x q, x in {0,1}, a<q, b<q+1,
at even q=2r the starting carry is a=2 floor(a/2)+y_q. If the carry c at q+2 has a further edge, it satisfies the same parity relation. Therefore the two reverse steps map scaled c to scaled a:
    u = 4 floor(c/2) + 2 y_(2r+2) + y_(2r+1),
    floor(a/2) = (u mod (2r+1)) mod r, u<4r+2.
The fold is the union of offsets 0,r,2r+1,3r+1, and the two exceptional zero-residue inputs u=2r or 4r+1. Those cannot be dropped in delayed carry, unlike a strict-interior modular proof.

The fixed target window has length n. The source bridge fixes all target bits from the already-known low word; it needs no assumption about future selected digits. Starting a reverse cover two clocks before the terminal clock is conservative and preserves all genuine paths. At each midpoint the even-clock parity recovers the full carry, and exact inverse recovery determines the preceding low word. Complement symmetry lets us retain only B mod 4=1. A certified empty cover below practicalCut gives critical reset nonreachability without separate margins.

## New formal interval work

Agent9's earlier [45954098366](https://github.com/FlareZ123/bb6/actions/runs/45954098366) extends the formal modular frontier to 113910. Two disjoint additional interval checks dispatched by Agent43 succeeded:
- [45973416940](https://github.com/FlareZ123/bb6/actions/runs/45973416940): 113912..124832 inclusive, 5461 even indices.
- [45973423344](https://github.com/FlareZ123/bb6/actions/runs/45973423344): 124836..164444 inclusive, 19805 even indices.

Together these add 25266 indices. The delayed gap 124834 is not included. 164446 is the next numerically known delayed exception. The earlier overlapping adaptive schedule run was cancelled and is superseded for source checking.

## Candidate n=124834

Independent JavaScript exact integer calculation, h=62416, gives the following conservative half-cover counts and midpoint carries:

| s | parents | surviving next carries |
|---:|---:|---|
|1|1|185376|
|62417|1|170250,206022|
|124833|2|113271,191131,182771|
|187249|3|none|

Thus the candidate is empty at s=249665, so n+s=374499 is below practicalCut(124834)+1. This is not a new numerical extinction record; previous numerical evidence was stronger. The new purpose is a source-level kernel certificate. gen_lag_pair.py emits chunked dense and sparse covers and recovery checks. The finite workflow has been dispatched; its conclusion is not claimed yet.

Local Python and container tool calls return ClientError; Lean was checked by the exact 4.36.0-rc2 CI environment. Concurrent main branch CAS conflicts were retried using the original content blobs, not forced updates.
