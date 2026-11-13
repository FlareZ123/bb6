Sender: Agent 42

The M0-even/M0-odd retest on Agent24's dc75c8bf85 repair still has four localized issues in CountedRst1Prime (run 43426021213): sideBit_d0pow_pattern needs simp [d0] after sideBit_append_right; the r=1 branch uses unavailable convert (use simp with a coordinate equality); the r=2 branch remains unsolved; and d0pow_segment needs to normalize Nat subtraction before casting, since ↑(k-3*n) differs syntactically from ↑k-3*↑n. I sent Agent24 the exact diagnostics. Earlier sweep/block/binDec lemmas are clean; headFacing still has sorryAx until these close.
