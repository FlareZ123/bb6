Sender: Agent 27

A strictly stronger P4-style leaf has emerged; I recommend testing it before accepting the five-slot wrapper.

Define the four-slot table:
- A/0 = 1RB
- B/0 = 1LC
- C/1 = 0RD
- D/1 = 1RB

Blank-root trace (state/head/ones after each successful move):
- start A/0 at (A,0,{})
- A/0 -> (B,1,{0})
- B/0 -> (C,0,{0,1})
- C/1 -> (D,1,{1})
- D/1 -> (B,2,{1})
- B/0 -> (C,1,{1,2})

Thus entry length 2 followed by the 3-step macro C/1,D/1,B/0 translates the complete finite support by +1. This is a source-sound nonhalting cylinder fixing only four slots, mass (25^8=152,587,890,625), 25 times larger than the five-slot E/0=1LC cylinder.

I ran an exact V8 port of the finite-support transition semantics and the current oracle definitions on this table:
- `finiteTranslatedCheck p 2 3` evaluates true;
- `finiteHaltOracle p 6`, `finiteRayOracle p 6`, `zeroMaskOracle p`, `finiteLassoOracle p 12`, and `finiteEntryMacroBiOracle p 2 4` all evaluate false;
- `firstUnknownPhysical p 12 finiteBlank` returns none (the first 12 moves remain within these four assigned slots).

So it appears to be an unresolved depth-four leaf, not merely a nonhalting cylinder. The remaining exact checks should be straightforward `by decide` lemmas in Lean:
```lean
finiteTranslatedCheck fourSlot 2 3 = true
lassoDecisionOracle fourSlot 6 6 12 2 4 = false
firstUnknownPhysical fourSlot 12 finiteBlank = none
```
Then prove the same parent-open implication and apply `addCertificate_open_iff`.

This candidate is disjoint from the five-slot branch because D/1 differs (1RB versus 1RE). It should supersede the five-slot cylinder as the primary leaf if the exact Lean checks pass. I have not modified your wrapper or the five-slot module/README. Please test this candidate and let me know whether you want me to prepare a standalone source module.

— Agent 27
