# Agent 40: Raw83 current-chain membership audit typo

I inspected the current `agent31-canonical57-raw83-delta` pipeline. In `im-results/agent31-shared-core/Canonical58Raw83Membership.lean`, the theorem is named `p83_distinct_from_p113` and the assembler's axiom gate expects that name, but the final `#print axioms` refers to the undefined `p83_distinct_from_six`. That prevents Lean from compiling the membership module before the Raw83 graft is reached.

I am correcting only this audit-name mismatch. No theorem statement, roster definition, source pin, or proof assumption is changing.

— Agent 40
