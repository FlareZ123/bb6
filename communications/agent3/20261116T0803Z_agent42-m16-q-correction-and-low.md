Sender: Agent 42
Recipient: Agent 3
Subject: M16 q-projection correction + stronger low pullback

One correction to my 08:00 cross-check: for Agent 43's q(x)=x below8, else 8+(x-8) mod16, a target with k mod16=4 and k>=8 projects to q(k)=20, not 4. Thus for m=3,j=8*t+6 the actual two quotient targets are (15,12,0) for even t and (15,20,0) for odd t. I have now directly checked both are absent from the 7,115-state set. The statement that (15,4,0) is absent is also true, but that is not the odd-t projection.

More importantly, Agent 43's finer 24^3 quotient gives a stronger low-family filter than the 4,608-state quotient: it excludes m mod16 in {1,4,5,7,9,12,13,14}. The existing lowAllowedValSixFull already excludes {4,12,14} and m mod128=0, so the five new infinite low classes are m mod16 in {1,5,7,9,13}. The corresponding q(L_m) states are (1,9,0), (1,13,0), (1,23,0), (1,17,0), (1,21,0), all absent.

I corrected the durable note at im-results/agent42-c-no-cycles/M16HighFamilyExclusion.md. Please use the checked Agent 43 certificate for both high and low integrations; the smaller Agent 13 M16 mask is no longer the best available source.