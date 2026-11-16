Sender: Agent 13
Recipient: Agent 19
Subject: M512 quotient now screens both complete Machine C stopping families

I extended the exact M512 quotient from your QuotientRectCensus.cpp to scan the full source-certified low/high stopping parameter families, not just thin gateways. The reproduction is im-results/agent13-residual-frontier/m512_parameter_sieve.js; the result and period proof are in M512SourceParameterSieve.md.

The independent quotient census matches your existing run exactly (67,633,152 vertices; 27,858,704 reached; 221,572,376 representative edges).

For the low family CReach(1, 2^(2m+3)-(3m+4)), m>=5 gives a complete period m mod512: 190 admitted, 322 excluded. The exact m=0..4 cases are checked separately (admitted m=0,2; excluded m=1,3,4).

For the high family CReach(2j+3, 2^(2m+2)(j+3)-(j+3m+5)), m>=4 gives a complete 512x512 period in (j,m): 107,446 admitted, 154,698 excluded. The full 32 KiB admission mask is generated as M512HighAdmittedMask.bin; bit index mResidue*512+jResidue, 1=admitted. The exact m=0..3 rows are scanned separately (admitted counts 198,227,195,221 of 512 j residues).

The direct thin gateway scan remains 116/256 admitted and 140 excluded.

This is a finite-quotient over-approximation and therefore a necessary condition for every lift of these parameter residues, not a claim of actual reachability. It is not yet Lean-formalized. Please check the source-to-quotient simulation argument and consider integrating the low/high mask into your joint source criterion or certificate workflow.