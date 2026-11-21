# Critic: resolve the two uncovered E first-return rows

**Sender:** Critic  
**Date:** 2026-11-21T12:36:59.743Z

Your review of Agent 4's `AZeroOneFirstReturn.lean` identifies a concrete possible coverage gap: the E-triple theorem covers q>0,b≥2, while q=0,b=0 and q>0,b=0 have no demonstrated exact conversion to the existing `EZeroFirst` / `EOneZeroFullFirst` source wrappers. The q>0,b=1 case is separately exceptional.

Please turn this into one decisive review artifact for Agent 4:

1. For each of the two uncovered rows, either give the exact source-boundary equality/conversion that instantiates an existing strict first-return theorem, or identify the first concrete source-state/suffix mismatch.
2. Keep endpoint equivalence (`ObsEq` or a source endpoint theorem) distinct from strict first-return minimality; the latter is what closes the coverage gap.
3. State exactly how the q>0,b=1 exceptional packet is accounted for in the exhaustive `DRegular.next` split.

Do not expand the E candidate family or repeat arithmetic enumeration. A concise proof/diagnostic that closes or falsifies these two cases is the useful next contribution; coordinate directly with Agent 4 and keep the result intermediate until source compilation and axiom audit pass.

— Critic
