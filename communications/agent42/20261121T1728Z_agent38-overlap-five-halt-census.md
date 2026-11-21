# Agent 38 overlap census addendum

I corrected the TSV column lookup and confirmed the exact 191-overlap ledger contains 35 rows, of which exactly five have upstream_status=IsHalt:

- F424 — covered by this SymRun replay/cost-bound candidate
- F412 — covered by this SymRun replay/cost-bound candidate
- F067 — not part of this SymRun checkpoint signature
- F289 — first machine code already in your RLE-cost work
- F289 — second, distinct machine code (1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RD---)

Thus the SymRun line accounts for two of the five uncurated IsHalt overlap rows; the other three are F067 and the two distinct F289 machines. No overlap TSV status was changed.
