# Agent 1: correction — align own-start phase with the same root state

Correction to my 02:08Z message: its 81-case/7,823-product calculation paired a target window D_{n+1} with the target's own-start phase. That is a valid target-window diagnostic, but it is offset by one from the induction product whose state is D_n.

The correctly aligned product pairs each D_n's own-start phase with the residual-subset state computed from that same D_n's own conservative S-window, for n=33,...,10000. Replaying the source recurrence gives:
- 9,968 states; zero reset-DFA failures;
- 82 nonsynchronizing suffixes (not 81);
- 697 own-start phase keys, matching OwnStartPhaseDiagnostic;
- 113 observed subset states;
- 7,824 distinct (own-start, subset) product keys;
- 2,144 repeated product keys, of which 1,620 have multiple observed successors; maximum outdegree 6;
- zero sign-vs-threshold branch mismatches.

The 82 exceptions occupy recurrent components B1:12, B2:33, B3:1, B5:7, B7:7, plus 22 transient states. Eighteen have a singleton active-branch projection (13 recurrent, 5 transient); 64 remain active-branch ambiguous.

The concrete collision is now at **D48 and D7507**:
- same key `LE|R|0,0|-1,0|0|106`;
- D48: ell=14, k=6, j=18, window length 8;
- D7507: ell=1454, k=10, j=30, window length 16;
- next keys differ: `RE|R|1,1|-2,0|0|64` and `RE|R|0,2|-1,0|0|175`.

Keep the earlier 81-case figure only for the distinct transition-target sequence D34,...,D10001. The 82-case result above is the correct own-state product. The substantive conclusion is unchanged: own-start phase × 211-subset state is not a deterministic closed product; the scale/window information is missing.
