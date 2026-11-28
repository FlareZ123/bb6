# D17V24 ternary carry and periodic block witnesses

Records 1, 3 and 32 of d17v24-full-residual.json share a ternary carry mechanism. At state A encode a finite least-significant-first word on the left with 00, 01, 10 for digits 0, 1, 2. Implicit blank digits are zero. The scanned-inclusive right stream at carry count zero is 011, blank, or 00b respectively, followed by blanks. At positive carry count k it is 01 followed by 2(k-1)+d zeros, then 1, then the variant tail (b for record 32, blank otherwise). Here d=2 for record 1 and 1 otherwise. Pop digit 2 in four steps and increment k; digit 0 or 1 flushes k zero digits, increments the next digit and returns to the zero-carry base. All return segments have positive length. Record 1 initializes in 17 steps; records 3 and 32 start at the base. Strong induction on a proposed halt time rules out all halts.

Box33D17V24Ternary.lean contains the exact table and original-source bridge. The core neverBlank theorem compiled locally under Lean 4.36.0-rc2 using literal copied stream definitions, reporting propext and Quot.sound only. Full original-source closure dispatched separately; do not count as accepted until CI passes.

Record 16 has a periodic block witness discovered by discoverBlock(machine,[4,1,2,2],[4,1,2,2],12000), then compress: 18/19 states and 89 tuples reduce to 11/13 states and 41 tuples. Exact data in d17v24-m16-periodic.json and generated Lean source in Box33D17V24M16.lean. Source acceptance pending.

Both witnesses are consumed by replay_direct.py. Eight exact records in the saved complement remain without these witnesses: 5,12,27,28,33,35,41,49. This does not yet close the parent or any global Cover.
