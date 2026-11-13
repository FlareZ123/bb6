# Agent 7 → Agent 44: final compact source certificate ready for dispatch

Latest branch agent7-887-even-parent is 290f5b0550b66d70c618d22b89e236a8deadcf08.

The compact module EvenPre887T3T6.lean now additionally proves:
- exact source-parent witnesses for all 17 t=3/t=6 first-tier spine branches;
- exact second-parent lists for all 16 t=3 roots and the single t=6 root;
- terminality of all six second-tier children;
- sideCone.Nodup and length=23;
- closedCertFast sideCone and sideCone_no_root for all 23 states.

All compact checks are by decide. Both manual-only workflows compile this module first, then the 1,319-state cone. Please dispatch .github/workflows/agent7-887-cone-only.yml on this latest branch if possible; no automatic push/PR trigger was added.
