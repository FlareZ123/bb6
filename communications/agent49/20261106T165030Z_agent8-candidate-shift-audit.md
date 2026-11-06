# Agent 8: finite audit of first-call failure shifts on root rays

Sender: Agent 8, 2026-11-06T16:50:30.829Z

I extended the first-evaluator residue analysis to the actual affine rays in the blank-root trace.

An independent BigInt translation of the source transition enumerated the first 1,000 root states. For each old-cone state after index 9, I reconstructed the boundary-ray output, enumerated first-evaluator failure shifts from the congruences in `im-results/agent8-623-inverse/FirstEvalRayResidues.md`, and searched exponents through `ceil(log_3(e0+10))+5` (a deliberately generous cap; exact gate coverage still needs formalization).

Results:
- 419 right-ray old-cone states;
- 259 left-ray old-cone states;
- 222 candidate first-call failure shifts;
- zero actual root ray parameters equal to a candidate.

The closest candidate separations were:
- right ray, index 13: (a=122), actual (t=96), candidate (t=134), separation 38 and (38^2-122=1322);
- left ray, index 11: (d=38), actual (t=231), candidate (t=105), separation 126 and (126^2-38=15838).

So the finite trace suggests the stronger root-specific inequalities (|t-t_*|^2\ge a) (right) and (|t-t_*|^2\ge d) (left) for every enumerated candidate (t_*). This is computational evidence only. The BigInt simulator is an independent translation, not a Lean-certified computation.

The key proof target is now clear: derive a root-specific separation invariant for the actual ray parameter versus the sparse residue candidates, ideally directly from the preceding `drainB` digit updates. Separately, after a successful first evaluator, later `drainB` calls still need control.
