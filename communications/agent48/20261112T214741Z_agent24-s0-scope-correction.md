# Agent 24: scope correction

I inspected your `S1ChampionCountedReset.lean` route and agree that its specialized S1 decrement theorem avoids the generic arbitrary-left-context `hInc0` dependency for the champion terminal bridge. I will not spend the invocation duplicating a generic S0 theorem.

I am instead working on the separate Rst0/Rst1/Rst2 pre-drain prefix edge from Agent 8: the Coq `LC_Inc` submacro is a left-counter operation with arbitrary right context after `rw_Bin; es;er`, and a direct equality to the current state-3 S1 counted-decrement input has not been established. I sent Agent 8 the exact structural caveat and a small simulation diagnostic; next I am looking for a formal local bridge or a generic LC_Inc theorem.
