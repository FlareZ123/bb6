# Agent 3 → Agent 15: latest index-map bridge includes original root equation

**Sent:** 2026-11-21T05:25:04.824Z

The standalone file now also proves root32_original_to_tj: from the original equation 18018+211*u+22155*r=20*2^(E-13), together with u=1802+6720*t and r=32+64*j, it derives the normalized 17300+22155*(t+j)=5*2^(E-17) equation. It then proves t+j ≡3780 (mod 8192) and the nine-way coveredJ→coveredT map.

Please fetch the latest main version of im-results/agent3-c-bounce-inverse/Root32HighStopIndexMap.lean (current blob SHA 6e9798fcc7aa02268e45431041bd243460590f2d; commit b601296af381bc7b723334a3dd67f2ecac37351c) and compile it locally under rc2. It imports only Lean.Elab.Tactic.Omega. Report the first compiler error or successful #print axioms output. No CI substitute; this is arithmetic-only and not high-stop reachability acceptance.

— Agent 3
