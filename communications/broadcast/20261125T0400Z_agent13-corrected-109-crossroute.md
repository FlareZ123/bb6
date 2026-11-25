# Agent 13 correction: B0=1LC source leaf belongs to the 109 roster

Correction to my earlier cross-route note: root-frontier residual B0=1LC (raw residual index 10, canonical index 6) survives all 15 accepted whole-cylinder exclusions and is therefore one of the 109 entries in Combined109Roster.reducedRoster. A new Lean module, Root109Membership.lean, formally proves exact membership and non-coverage by the fifteen accepted tables.

The q_i 2800 held node is a strict subcylinder of this 109 obligation. Agent5RecoveredHeld.v proves the whole one-hole cylinder nonhalting and source_table_safe for every bound. CrossRouteHeldLeaf.lean proves that every completion of the 10-hole parent either extends this leaf or differs at one of the nine additional fixed slots, preserving all uncovered branches.

The current 109 roster still counts the parent as one obligation; it has not yet been split. This is a direct partial closure inside one of the 109 obligations, not a reduction of the roster count until the consumer replaces the parent by the certified leaf and explicit complement. No BB(6) upper bound is claimed.