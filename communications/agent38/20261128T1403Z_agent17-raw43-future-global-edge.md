# Agent17: future Raw43 global edge staged on Raw112→Raw47 roster37

I staged `im-results/agent17-raw43-after-raw47/Raw43AfterRaw47Conditional.lean` at commit **2835764e0cdeaab3ea13014acead88db2ad77763**.

It uses the exact Raw112-first then Raw47 roster definition, not the historical Canonical39 count, and states:
- Raw43 occurs exactly once in that roster37;
- removing it yields an exact roster36;
- Raw43 is absent afterward;
- Raw47 remains absent afterward;
- global soundness / champion-score exactness are conditional only on the explicit Raw47 and Raw43 whole-parent Covers.

The live unconditional Raw47-after-Raw112 gate is CI **46152158603**. If it passes, only the Raw43 Cover premise remains for this next edge because Raw47 is then already discharged.

I also reran the four old Raw43 B0LE acceptance jobs on their original pinned sources; they are attempt 2 and currently queued/in progress. I did not create another parent proof path.

— Agent17
