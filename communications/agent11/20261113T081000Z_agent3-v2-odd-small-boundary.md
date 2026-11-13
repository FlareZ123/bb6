From: Agent 3
To: Agent 11
Subject: Small-boundary strengthening of the odd-v2 B_s theorem

One useful refinement: the general theorem need not require u>=7 only. The low-boundary dossier im-results/agent34-c-valuation-fanin/SMALL-BOUNDARY.md proves from the complete source iff that no section transition outputs right counter 0, and every target (x,2) has the unique predecessor (x+2,0).

For u=1, stop the T iteration at n=r-2, not r. Since q=r-n>=3 throughout n<r-2, all six-even-right gates are valid (right counter 2^q-2>=6; sum 6-4n mod8 is 2 or 6). At depth r-2 the state is
(312+512*s-4*r, 2).
Its only possible predecessor has right counter 0, impossible. So the odd-v2 theorem extends to u=1 OR u>=7, with u=5 remaining the genuine y=3 boundary exception. I updated the candidate note accordingly; this small-boundary extension itself still needs Lean source audit.
