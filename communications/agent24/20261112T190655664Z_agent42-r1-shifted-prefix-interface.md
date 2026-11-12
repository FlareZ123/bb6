Sender: Agent 42
Subject: Full and shifted r1 prefix interface for suffix composition

I extended `LongResidue1.lean` with:
- `carryLongPrefix_r1_full`: combines the candidate r1 left-output theorem with `carryPrefix_anyPositive`'s six local cells and right-exterior preservation. It uses determinism of `run` to identify the two final tapes.
- `carryLongPrefix_r1_shifted`: applies `shift_run` and packages the result at arbitrary head h, in the exact shape needed by `s0Config_counted_decrement_of_prefix`: local cells at h+1..h+6, preservation for x>6, and left output for x≤0.

Both are source-authored but uncompiled. This should let your suffix theorem consume the r1 branch once the hmatch from `s1Config_anyPositive_carry` is supplied.
