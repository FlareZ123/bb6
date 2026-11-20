# Agent 37 follow-up: regular-branch formulas from the boundary replay

The boundary-marker simulator also reproduces the regular-section B/E transition formulas in `DRegularFirstExit` and the source lemmas. These are computational cross-checks over representative parameters; the existing Lean source lemmas remain the formal evidence.

## B branch (`a = 3k+2`)

For input suffix `(01)^q 1^b`, the 5-step tail gives:
- `q=0,b=0`: `A(8k+9, [])`;
- `q=1`: `A(8k+10+b, [])`;
- `q≥2`: `A(8k+10, (01)^(q-1) 1^b)`.

This matches the three B cases in the first-exit table. The generic source lemma `DRegularBSource` covers the q≥2 case.

## E branch (`a = 3k+4`)

For input suffix `(01)^q 1^b`, the canonical tail counts and outputs are:
- `q=0,b=0`: `n=13`, output `A(8k+5, (01) 1^5)`;
- `q>0,b=0`: `n=13+4q`, output `A(8k+5, (01) 1^(2q+5))`;
- `q>0,b=2`: `n=17+6(q-1)`, output `A(8k+9, (01)^(q+1))`;
- `q>0,b≥3`: `n=21+6(q-1)`, output `A(8k+9, (01)^(q+2) 1^(b-3))`.

These match the output forms in `DRegularELow`, `DRegularETwo`, and `DRegularESource`. The E, b=1 case is the exceptional `next = none` branch.

The formulas were checked by exact finite-tail simulation on multiple q,b values (including q through 3 and several b values), with the marker parity and alternating-block precondition checked. They are not yet formalized as a general Lean theorem.

## Why external A_step2 counts sometimes differ

The external proof may use a longer finite tail than the canonical count above. If the finite tail is extended by 2t steps while the alternating block shortens by t pairs, then `n + 2m'` is invariant. The full post-expansion duration `n + 2m' + 2` is therefore unchanged. Example: the E,b=2 transition from `(q,b)=(1,2)` has canonical `n=17`, while the external trace uses `n=21`; both cuts produce the same endpoint and total duration.

## Exceptional exit to align

The first ten external A_step2 outputs have regular suffix parameters
`(1,5),(3,2),(2,2),(1,2),(2,0),(1,0),(1,7),(3,4),(2,4),(4,1)`.
At `(q,b)=(4,1)`, the regular DRegular transition is undefined. The external proof's call 11 uses `n=35` and produces
`0111111110111111 = 0 1^8 0 1^6`,
a packet-shaped suffix with `fixedTail=0 1^6`. This is the concrete endpoint to compare with the exceptional E / packet closure proofs. Its suffix shape alone is not enough to identify a theorem: compare the full unary parameter and source configuration before claiming equality.
