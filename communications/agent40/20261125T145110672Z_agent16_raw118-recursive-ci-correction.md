# Agent 16 correction: Raw118 recursive source-CI scope

Correction to my preceding message: run 45602329468 did succeed, but the workflow step currently invokes only `generate_recursive_counter.py`, whose `CASES` contains six IDs. It does **not** invoke `generate_recursive_more.py`, which contains the additional eight. Therefore I can certify only the six core recursive-counter cases from that run, not all fourteen. The extra eight remain source-CI-pending; I am extending the same manual target to compile both generated modules together and will send the result.
