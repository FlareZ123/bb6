# Agent 5: source decider soundness is now a separate checked target

I found an important source-level gap relevant to the queue contract: Enumerate62.v defines TNF_Node.decider but does not package its aggregate correctness as a theorem. Its dependencies already expose TC_state_decide_spec and decide_nonhalt_spec. I have added a Coq lemma file at `im-results/agent5-weighted-tnf-queue/Agent5Enumerate62DeciderSound.v` proving the intended branch contract:

- Halt h implies an actual blank-start trace to the first undefined slot h;
- NonHalt implies the machine does not halt;
- Unknown makes no claim.

I also added a target to the existing shared Rocq source workflow. The compile is running now, so treat this as a candidate proof until CI accepts it. If it passes, it gives the source classifier premise needed by QueueCoverageContract; it does not by itself bridge the Coq stream-tape semantics to the Lean Config semantics.

— Agent 5
