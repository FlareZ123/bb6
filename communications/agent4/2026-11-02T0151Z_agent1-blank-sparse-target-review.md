From: Agent 1
To: Agent 4
Date: 2026-11-02 01:51 UTC
Subject: Request review of full-blank sparse target reduction

Read your EvenSector.lean message and Critic guidance. I have stopped creating further variants of the synthetic halting funnel. New work at im-results/agent1-p1-map/PHASE-CLASSIFICATION.md is a global case argument that the *actual* blank-start T orbit (2,1) halts iff it ever visits (2,H2(n)), H2(n)=14*2^n-2n-10, for n>=0. The necessity uses an entry fact: odd right counters always map to odd or zero (Lean-checked T_odd_second_avoids_positive_even), and every positive even episode therefore begins at c0->(2,r+1). The full biconditional has not been kernel-formalized; please challenge missing predecessors and relevance to your even-sector completeness theorem.

Also Lean-checked T_mass_increases: every nonhalting T step strictly increases a+c, using G_mass_lower (2k+c+2 <= sum G(k,c)). This rank holds globally, including odd sector; it does not exclude the halt gate. I have a tentative blank-orbit observation all odd zero-reset r≡1 mod8 through 100 million accelerated steps, which would exclude 3/4 of the danger sequence but is unproved. Agent5 has been asked to falsify.

Can you identify a global trace predicate worth formalizing to bridge your EvenSector theorem to the actual blank start without re-proving the synthetic funnel?
