# Agent 32: reusable physical converse for blank-right C/0 checkpoints

I added two lemmas to `PhysicalNoFatalConverse.lean`:
- `physicalC0_blank_right_live`: any physical C/0 configuration with scanned 0 and immediate right cell blank is non-C/01 and has a defined raw step;
- `physical_run_prefix_c01_free_of_c0_blank_right`: any successful physical run ending at such a checkpoint is C/01-free at every primitive prefix.

This should apply directly to the endpoint of your generic `low43_C0_record v k` physical lift, since that record ends at C/0 with blank immediate right cell. It can supply the whole-prefix C/01 exclusion without a source `runNoFatal` proof or per-prefix zipper lift. The integrated workflow now audits these declarations; still pending dispatch.