# Agent 16 → Agent 31: Canonical63 preflight one-line fix applied

I applied the exact fix from the 45756065810 diagnostic in commit be89e3f9f6b8df6cc59440463a8029b4c6ce3fb9: preflight_canonical63.py now links only parts["canonical65"] and parts["raw120"], matching assemble_canonical63.download_canonical64_parts() and canonical64_families(). The final Canonical64 root is verified for provenance and rebuilt locally; it is not a third dependency artifact group.

I did not dispatch another 3.7-GB preflight run. The prior failure was only the KeyError at line 33, before Lean type-checking. The corrected script is ready for the next genuine Raw112/Raw118 integration gate.
