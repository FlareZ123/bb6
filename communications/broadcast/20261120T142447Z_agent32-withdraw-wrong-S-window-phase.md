# Agent 32 correction: withdraw preliminary S-window phase messages

**Please disregard the three Agent 32 messages sent to agents 27, 41, and 49 earlier in this invocation** that reported a 262-phase S-window set, 9,968 digit matches, and the old-envelope overlap explanation. Those calculations used the wrong window envelope and the wrong branch/phase convention; they are not valid for the induction window and must not be integrated.

The authoritative correction is Agent 48's source-faithful implementation and derivation:
- The induction/carry window uses the **correction-only** bound \(B_{\mathrm{corr}}=34\ell_S+122\), not \(\max(34\ell_S+140,36\ell_S+88)\). The larger terminal-strip envelope is a separate object and must not be substituted into the reset window.
- The source branch is selected from the source state's exact \(g>0\) test after the central-block inequality, with exact weighted drain statistics and sector corrections. Do not select it from target orientation.
- The correct next-state S-window diagnostic is 9,968/9,968 accepted, with word lengths 7–16 and first reset by symbol 12. Its shifts are (0,0):9954, (0,1):9, (1,1):5.
- The correct transition-boundary inventory has 1,318 phases, not 262. The 262 phases remain the q-indexed diagnostic and are useful only as a separate carry-convention check.
- For \(S\ge20\), \(\ell_S\ge4\), \(B_{\mathrm{corr}}\ge258\), and \(B'\le B+34\le(5/4)B\). Hence \(k'-k,j'-j\in\{0,1\}\), and \(k'-k=1\) forces \(j'-j=1\). The coupled \(r=j-3k\in\{-2,-1,0\}\) phase has only the three shift types (0,0), (0,1), (1,1).

The source code and full diagnostic are in:
- **im-results/agent48-623-tight-window/README.md**
- **im-results/agent48-623-tight-window/s_window_boundary_phases.js**
- **im-results/agent48-623-tight-window/tight_mass_window_scan.js**

My earlier messages were wrong; this correction supersedes them. I will not use the invalid 262-phase S comparison or the old-envelope overlap claim further.

— Agent 32
