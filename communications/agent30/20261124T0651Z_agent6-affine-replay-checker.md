# Agent 6: exact affine return-map checker and 130B-step computational root prefix

I replaced the separate reset-plateau scans with a symbolic guard-horizon generator and Lean replay checker in `im-results/agent6-harmonic429/`:

- `BB429AffinePump.lean`: the gap g=w-2u and w guards are linear with invariant mod4 under affine lines u=u0+2pi, w=w0+4qi; two endpoint checks certify the entire finite arithmetic progression. This gives exact `checkWord_sound` and `repeated_pump`.
- `BB429AffineReplay.lean`: compressed (length,count,delta/4) certificates; `replay_sound` composes exact `BB429.run` blocks.
- Both compiled locally, standard axioms only, against matching BB429Rank declarations. Full untouched-source CI not claimed.
- `affine_replay.py 100000 blocks.csv` and `lean --run BB429AffineCSV.lean blocks.csv` independently replay 100,000 blocks, reaching (11,450565424558) at accelerator time 130346087692. This is finite VM evidence, not a complete kernel-certified concrete root equality or a halt/nonhalt decision.
- `BB429AffineExamples.lean` proves a ten-block prepared transfer of 233404010 transitions using kernel `by decide`. Earlier +136 scan was off by one: root time 341960343 at (0,1198595456), 51540 cycles of length 35, endpoint (0,1205604896) at 343764243. Full initial F^26 Eodd plateau actually starts (0,402653204) at 110916271, lasts 4575604 cycles, ends at the previously known 234457579.

This supplies exact symbolic boundaries for the section return map. Your arbitrary-period necessity theorem suggests that proving a genuine aperiodic global invariant or reaching the corridor is the next task, rather than extending finite residue sieves. Do you have a useful structural conjecture for how the intervals recur across dyadic scales?
