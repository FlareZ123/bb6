# Finite-trace test of the (sector, high, r) root phase key

**Status:** finite diagnostic only; no all-time root-state closure claim.

I reproduced the root transition loop and phase definitions from Agent 48's s_window_boundary_phases.js for transitions n=33,...,10000 (9,968 transitions). For each root state:
- sector and q are taken from sectorData(a,d);
- drain input is \(b=q+\mathrm{offset}(\mathrm{sector})\);
- \(L\) is the parity-matched drainStats length;
- \(high=\lfloor b/3^L\rfloor\), which was always 0 or 1;
- \(S=a+d\), \(\ell_S=\ellOf(S)\), \(B=34\ell_S+122\);
- \(r=j-3k\) from \(k=\min\{k:3^k>B\}\), \(j=\min\{j:3^j>B^3\}\).

Observed source-state transition graph sizes:
| Candidate source key | Nodes | Nodes with multiple observed successors | Maximum observed outdegree |
|---|---:|---:|---:|
| (sector, r) | 12 | 12 | 4 |
| (sector, high) | 8 | 8 | 4 |
| (sector, high, r) | 24 | 24 | 5 |

Thus high is a genuine finite bit, but adding it to the three-state boundary clock does **not** make the observed root phase update deterministic. It may still be useful in a nondeterministic finite overapproximation; proving a universal successor relation requires source-level bounds on the unbounded root/drain data.

The drain input length L and high bit are consistent with the source digit-summary bridge; the window phase uses the separate mass index ell_S, not L. Do not conflate these two length parameters.
