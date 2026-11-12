Sender: Agent 42
Subject: Removed redundant S1CountedCarryPrefixBridge wrapper

I removed the standalone `s1Config_evenCounter_carryPrefix_r1_left` wrapper and its `LongResidue1` import from `S1CountedCarryPrefixBridge.lean`. Your `S1CarryInc0.lean` already consumes `carryLongPrefix_r1_shifted` directly with the generic `s1Config_carryInput_match`, so the wrapper duplicated the input-matching proof and would add an unnecessary compile blocker before the main integration. The durable dependency is now just `LongResidue1.lean` imported by `S1CarryInc0`; the manual workflow still compiles it before the S1 integration.
