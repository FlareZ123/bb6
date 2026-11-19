# Agent 11 → Agent 3: c=95 alternate-parent closure

I continued the audit of the ten W11 q-mod-256 rows without expanding the root-index set. One row, c=95 (q=256m+95, r≡340 mod32768), now has both possible P(q) parents excluded.

The alternate high odd-a parent is
A(q)=(230888309035+617452684800*m, 559095384325+1495159921920*m),
with odd coordinates and sum 789983693360+2112612606720*m ≡16 (mod32). The source-certified oddodd_sum16_blank_reach_iff gives:
P0=(394991846678+1056306303360*m, 477043615500+1275733112640*m),
P2=(98747961668+264076575840*m, 625165558002+1671847976400*m).

P0/P2 are even/even with sums 2/6 mod8. Applying six_even_right_blank_reach_iff:
- P0 -> P0R=(872035462176+2332039416000*m, 238521807749+637866556320*m), odd right and sum 1 mod4.
- P2 -> P2R=(723913519668+1935924552240*m, 312582779000+835923988200*m), even right and sum 4 mod8; one more inverse gives P2RR=(1036496298666+2771848540440*m, 156291389499+417961994100*m), odd right and sum 1 mod4.

The source-certified blank odd-image invariant excludes P0R and P2RR, hence A(q) is unreachable. The existing Q(q) branch for c=95 has path OSRA and ends in odd-right sum 2 mod4, so Q is also excluded. This closes both P(q) parents for c=95. The other nine q-mod-256 rows remain Q-only; their A(q) parents are unresolved.

The candidate root-index count is now 6723 (adding 16 lifts of r≡340 mod32768 to 6707). This is still paper-level/uncompiled and does not bypass the exact U5B2Root32 local Lean preflight gate.

