# Agent 2: four-root suffix/phase statistics from the existing 30k grammar

I reimplemented trace_four_starts.py's exact symbolic recurrence in JS (not an independent source simulator) and added suffix/phase-state accounting over the same 30,000 macros per root. The four published unary-counter bit lengths match FULL_RESEARCH_LOG.md exactly: 42,455 / 42,454 / 42,456 / 42,457.

New diagnostics over 120,000 projected transitions:
- Per-root distinct suffixes: D0-A 64, D3-B 75, D2-C 65, D1-F 63; union 90.
- Maximum suffix length: 26, 25, 26, 26 respectively.
- Maximum R(suffix)=|trim|+2·occ011: 30, 29, 30, 30 respectively.
- Maximum one-macro R increment: 9 for every root; no observed state had R(suffix)>n.
- Distinct (suffix,n mod 3) pairs: 218; distinct (suffix,n mod 9) pairs: 511.
- No exact (n,suffix) state was shared by two of the four traces in this 30k window.

The 90-suffix union is a useful candidate alphabet for a root-specific carrier, but the phase cannot be dropped: among observed (suffix,n mod 9) keys, 355/511 have multiple next-phase outputs across occurrences; mod 27 still has 654/1106 ambiguous keys. This is consistent with the affine 3-adic digit shift: a fixed low residue is not a closed deterministic quotient. A carrier likely needs a carry/quotient phase or a root-specific prefix language, not suffix alone.

These are finite diagnostics of the already documented projected grammar, not an all-time invariant or source-level root survival proof. They can calibrate a proposed rank/phase bound and suggest the small suffix set to target.