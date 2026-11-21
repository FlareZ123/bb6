# Agent 5: corrected S4 Y/Z/F return maps and 15-digit period

I extended the Q/R/V/W/X/Y hierarchy with two correctly boundary-aligned return maps. The reproducible artifacts are:

- `im-results/agent5-s4-nested-depth6/DEEPER-RETURN-PERIODS.md`
- `im-results/agent5-s4-nested-depth6/s4_nested_depth6.mjs`
- Updated `im-results/agent5-s4-nested-depth6/README.md`

Exact BigInt results:

1. The ninth digit has period 5 under Y. Extracting (Z=Y^5) gives a pure 45,157-gate suffix word.
2. The tenth digit has period 4 under Z. Extracting (Z^4) gives (F=B_{p_F}\circ G_{w_F}), with 90,309 gates and pending addition (p_F=73,515,085,360,333,450,329).
3. Starting after one F application, the first 1–5 digits of the suffix after digit 10 have exact periods (4,16,64,320,1280), respectively. The full-stack scan survives 1,280 F blocks; stack length grows from 23 to 28 at block 12.
4. Consequently the first-15-digit projection reaches a witnessed period of 25,600 Y blocks after a 25-Y-block preperiod witness. This is a projection period, not a full-state cycle or nonhalting proof.

The pending-aware mass identity is
[
\sum_i (w_F)_i+2|w_F|+p_F=1024(20N_Y),
\quad N_Y=1,125,899,906,842,624,000,000.
]

Important correction: an earlier exploratory 45,190-gate continuation was off by one suffix digit (it applied F to `afterZ` rather than `afterZ.slice(1)`) and has been discarded. Do not reuse that K/L/... branch. The committed script uses the corrected suffix boundary and currently stops at F.

The concrete words and finite prefix periods are exact BigInt computations; the specific Y/Z/F certificates are not yet Lean-kernel checked. No S4 nonhalting proof or BB(6) bound improvement is claimed. Highest-value next steps are to run the updated script in manual CI, formalize the concrete boundary extractions and period certificates in Lean, and extend the F prefix-period law to deeper digits while seeking an all-time tail-growth invariant.
