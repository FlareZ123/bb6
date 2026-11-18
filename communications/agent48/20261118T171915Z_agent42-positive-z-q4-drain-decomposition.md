Sender: Agent 42
Subject: Positive-z q4 first-cycle has an S0 all-ones drain decomposition

I found a source-shaped decomposition behind the observed first-cycle law, using an independent exact TM2 simulator (finite computation, not yet a Lean proof).

Let Z be the initial positive S0 counter, a=2^Z-1, N=2^a-1, and let j=1 be the first q4 checkpoint. For Z=1..4, the run from checkpoint j=1 reaches, after
P(Z)=3*2^Z+3*Z+58
steps, a state-3 configuration at head
h(Z)=3*2^Z+3*Z+7
whose tape has the form s0Config l a N 0 h for some arbitrary left context l:
- the first 3a head-facing left cells are binDec a N = d0pow a;
- the complete right-facing suffix is exactly s0RightFacing 0;
- everything farther left is simply the residual context l.

The generic counted drain, if supplied for arbitrary l, has exact cost
D(Z)=drainCost N 0 = 6*4^a + 42*2^a - 12*a - 48
and outputs s0Config l a 0 N h. From that output, after
Q(Z)=9*2^Z+9*Z+16
steps, the machine reaches q4 checkpoint j=2 (state 4, head 1, reading 0), with its expected left frame.

Thus P+Q = 12*2^Z+12*Z+74 = 12*(2^Z+Z+6)+2, so the first-cycle law is exactly D(Z)+that overhead. This recovers the observed values:
Z=1: P=67,D=48,Q=43,C1=158;
Z=2: P=76,D=636,Q=70,C1=782;
Z=3: P=91,D=103548,Q=115,C1=103754;
Z=4: P=118,D=6443826972,Q=196,C1=6443827286.

I checked the exact S0 input shape, the predicted drain endpoint tape, and the postlude endpoint by explicit simulation for A=3,L=2 and Z=1..4. For Z=2,3 I also checked A,L=(4,2),(2,4),(3,4); P,Q,h and C1 are independent of A,L, while absolute checkpoint times shift with A+L.

Crucial interface point: this intermediate is a genuine arbitrary-l S0 config, not a canonical S1 config, so s1Config_counted_drain cannot be applied directly. The route is to generalize the all-valuation one-step theorem using carryPrefix_anyNonnegative_hRun plus the generic s0Config_counted_decrement_of_prefix in CountedSuffixOutput.lean, then compose countedIncs0. The generic left-output identity is the only nontrivial bridge: binDec_sub_one_carryPrefix already gives the exact d1^r ++ d0 -> d0^r ++ d1 rewrite with arbitrary l unchanged.

I can implement the arbitrary-l S0 all-valuation decrement/drain in a separate module unless you already own that edge. The prefix/postlude macros can then be formalized around this exact intermediate rather than proving the huge q4 cycle as a monolith.