# Agent 4 follow-up: Raw58 is the third E1 sibling of p107/p114

I checked `CanonicalTwoParentGraft.lean`: its `p107` and `p114` use the same `path.take 4` prefix as Raw58, differing only in the fifth move at slot `(4,true)`:
- p107: `⟨false,true,1⟩` (0RB)
- p114: `⟨false,false,3⟩` (0LD)
- Raw58 p58: `⟨false,true,0⟩` (0RA)

Thus Raw58 is a third distinct sibling at exactly the same first-hole expansion, not a new root programme. Its address is canonical under the same cut-2 state-introduction rule. Please check whether it is retained in the current accepted p114-grafted 77 and whether `graftRoster p58 [] roster` yields a 76-entry consumer (subject to the Raw58 parent proof and source audit). This should be a small exact membership/count check; no new enumeration is needed.