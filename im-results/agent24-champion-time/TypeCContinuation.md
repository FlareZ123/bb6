# Type-C continuation: an 11-step bridge into the existing q4 scan

**Status:** intermediate research. The 46-step theorem is independently compiled in a self-contained Lean 4.36.0-rc2 model that reproduces the repository's TM63 machine, Config/run semantics, finite configurations, frame lift and bridgeAt argument. The repository source module is aligned with that proof but has not yet been compiled against its actual transitive imports. No claim about BB(6)'s final value follows.

## The 46-step continuation

Agent 48's typeC_two_step_continuation gives state 1 at head h-7 after 35 moves. Its tape has ones on every cell h-7,...,h+2. The source-side right stream [false,false,false] ++ tailR supplies the third zero h+3, which is not part of typeCInput but is needed by the next bridge.

The exact 11-step finite configuration is:
\`\`\`lean
typeCPostSetupStart : FConfig :=
  ⟨1, 0, [0,1,2,3,4,5,6,7,8,9]⟩

typeCPostSetupEnd : FConfig :=
  ⟨4, 11, [10,8,5,2]⟩
\`\`\`
The exact source-table computation is
\`\`\`lean
fRun tm2 11 typeCPostSetupStart = some typeCPostSetupEnd
\`\`\`
and all eleven pre-step heads lie in [0,10]. This was checked locally with by decide.

Translated to the original head coordinate, the 11-step trace:
- starts in state 1 at h-7;
- reads the ten consecutive ones and the blank at h+3;
- ends in state 4 at h+4;
- writes ones at h-5,h-2,h+1,h+3 within the local window;
- leaves all cells at or beyond h+4 unchanged.

The complete 46-step arbitrary-tape composition and its right-tail preservation theorem both compile in the self-contained Lean model. Their axiom reports contain only [propext, Classical.choice, Quot.sound], with no sorryAx. The model copies the repository's TM63 transition table and source execution semantics; it is an independent preflight, not yet a compile of the repository's actual imports.

The repository source proof is in TypeCToState4.lean. It adds the finite 11-step certificate, bridgeAt lift, 35+11 composition, right-tail preservation, the h+3 guard from the right-side 000 prefix, and the full M-4 BinDec source family.

## The next macro

TypeCPrefix.lean composes the 46-step bridge with the existing first-cycle tail:
\`\`\`
Type-C 33 + two-zero setup 2 + state-1 bridge 11
  -> state 4 at h+4
  -> E_scan(m)
  -> two-zero setup 2
  -> state-1 d1-block scan(3n)
  -> q4Tail(29)
\`\`\`
Its expected total cost through q4Tail is m+3n+77. This module is a source draft and still needs compilation against the repository import closure.

## Evidence for the S0/Q continuation

A direct exact-table simulator was run for (m,n)=(3,2),(5,3),(6,4). In all three cases, after q4Tail the head-facing S0 word had the form
d0pow(n-1) ++ 1^(m+2) ++ [0,1,0,0] ++ tail,
and the right suffix was s0RightFacing(0). After the all-ones S0 drain and q4/S0 postlude, the next state-4 checkpoint had the type-A local window 00110000 and right-side shape
0^3 ++ 1^(m+3n+2) ++ 0^2 ++ 1^(3*2^(n-1)) ++ 0^4.

These are finite simulation observations, not universal theorems. The remaining source proof must:
- compile TypeCToState4.lean and TypeCPrefix.lean against the actual import closure;
- identify the q4-tail frame as the corresponding s0Config, including the finite right exterior;
- apply s0Config_counted_drain_closed;
- establish the residual 1^(m+2) ++ 0100 guard and apply q4S0Postlude_at;
- prove the next type-A local window and right-tail recurrence for all admissible parameters.

Do not promote this note to results/ until the complete source composition is kernel-checked and its transitive axioms audited.
