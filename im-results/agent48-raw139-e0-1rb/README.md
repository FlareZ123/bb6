# Raw139 E0=1RB: complete computational parent candidate

**Exact parent:** `[7,24,11,24,14,24,24,16,7,11,24,24]` (normalized row (2,1RB)). **Candidate weighted bound: 103019.** All ordinary leaves have computational witnesses; original-source Lean acceptance is pending.

The exact first-hole partition (limit 450, ordinary FAR dimension at most 2) has 16,948 splits and 389,805 leaves: 288,501 translated cycles, 64,523 initial last holes, 33,424 ordinary FAR, and 3,357 initially open. Each split retains all 24 ordinary moves.

Of the open leaves, 3,347 close using unreflected Block-FAR (2,935 width two, 412 width three), and ten are late last-hole witnesses. The longest is open index 613, table `[7,20,11,0,14,1,24,16,7,11,6,12]`, whose first undefined transition is slot 6 at 103013 steps. The next largest late query is 2434 steps. The proposed weighted bound includes the six-step allowance.

The last difficult Block-FAR closure, open index 2688, requires the width-three phase abstraction (cap 1, modulus 1, six remembered symbols), with minimized left/right dimensions 368/1012. Its size and the 103013-step last-hole replay may make the original-source kernel audit expensive; computational completion does not establish formal acceptance.

## Reproduction and acceptance

Run `bash im-results/agent48-raw139-e0-1rb/reproduce-parent.sh` from repository root with Lean 4.36.0-rc2. The existing scanner reproduces SHA256 `2ab1b14dea5234bdd5c4dbc50280c4d86211d3d1a2f38ca4e06ecc74347445d0`. The exact extra parameters, late tables and assignment digest are in `discover.py`. The sharded audit generator now checks late first-hole witnesses by direct linear replay, then generates the ordinary original-source kernel certificate.

Existing manual workflow `agent48-raw139-f1-siblings.yml`, kind=e0parent, sibling=OneRB. Intended theorem `BB6.Agent48Raw139E0OneRB.all_completions_weighted`. After successful source audit, integrate using explicit normalized membership and Cover monotonicity. No global bound or roster reduction is claimed.
