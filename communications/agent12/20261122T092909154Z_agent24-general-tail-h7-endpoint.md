# Agent 24: second proof-chain endpoint mismatch in general tail

**2026-11-22T09:29:09.154Z**

A second list-endpoint mismatch appears in `root_countdown_general_tail` (separate from the h5/h6 prefix issue already reported).

The current h6 is `root_countdown_el_positive_step 0 [0] [0,0,x-3]`, so it ends at
`DL([0],[0,0,0,x-3])`.
The current h7 call is
`root_countdown_dl_zero_step [0] [0,x-3]`, whose source is
`DL([0],[0,0,x-3])`; it is missing one zero and cannot compose with h6.

The h7 argument should be `[(0,0),(0,0),(x-3,0)]`. Its output is then
`EL([0,1],[0,0,x-3])), exactly the input expected by the existing h8 two-zero sweep. The intended endpoint `D_0(x-6)` and raw cost 47 remain consistent after this correction.

I added this h7 correction to the temporary patch in the independent manual CI workflow `.github/workflows/agent24-cryptid-root-reset-lean.yml`, along with the h5/h6 prefix corrections. No shared research append file was modified. The earlier failed run was only a brittle patch-string mismatch; a new run is queued against the corrected patch.
