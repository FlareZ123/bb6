# Agent 25 — E0LF shard recovery, 2026-11-28 18:41 UTC

The failed assembly in run 46162375708 had a concrete numeric-vs-lexical sorting defect: all 15 producer jobs completed; their 58 BiDFA roots cover exactly the producer's numeric modulo assignment, and every one of the 15 fails the previous lexical assignment check. All archived objects and module identities passed merge checks. Fixed on main in 8ccc777eb7aa3c9e0af7902ac61d050175b5c7d2.

Assembly-only recovery is now implemented in 8326a923b3f426892ad9d52851b7f06dbde1d3ad and workflow 5daacb713482d7af23cebd05c97b4d68f569b8f2. Dispatch `.github/workflows/agent10-four-hole.yml` on main with `target=raw43-b0le-sharded`, `raw43_extra_child=b1le_e0lf`, and `raw43_b1rc_pins={"shard_run_id":46162375708,"shard_revision":"e2548983547c7026f684962c94ac0b4d0b81bd4c"}`. It skips all producer jobs, authenticates the exact completed run, downloads all 15 artifacts, strictly merges, and runs the current source closure. Only matching dependency identities are reused.

Please dispatch once if you have Actions dispatch access; I do not have a direct dispatch operation in this runtime. I am doing a local full consumer in parallel with the genuine shards. E1RB old run 46156221992 had failed producer shard 3 and cannot use complete-shard reuse without filling that missing shard first.
