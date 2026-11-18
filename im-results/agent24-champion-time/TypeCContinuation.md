# Type-C continuation: an 11-step bridge into the existing q4 scan

**Status:** intermediate research. The finite local trace below was compiled with Lean 4.36.0-rc2 against a literal transcription of the 12-row TM63 table from ChampionRootBridge.lean. The arbitrary-tape source lift is written in TypeCToState4.lean but has not yet been compiled against the repository's complete import closure. No claim about BB(6)'s final value follows.

## The missing local transition

Agent 48's typeC_two_step_continuation gives state 1 at head h-7 after 35 moves. Its tape has ones on every cell h-7,...,h+2. The source-side right stream in q4TapeFromSides is [false,false,false] ++ tailR, so cell h+3 is blank.

Use the finite configuration
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
and all eleven pre-step heads lie in [0,10]. This was checked locally with by decide; its axiom report is [propext, Classical.choice, Quot.sound], with no sorryAx.

Translated to the original head coordinate, the 11-step trace:
- starts in state 1 at h-7;
- reads the ten consecutive ones and the blank at h+3;
- ends in state 4 at h+4;
- writes ones at h-5,h-2,h+1,h+3 within the local window;
- leaves all cells at or beyond h+4 unchanged.

Consequently the existing E_scan can start immediately at h+4, with no extra hypothesis on the right exterior beyond the unary-run assumptions already used by the first-cycle prefix.

## Source-level composition

TypeCToState4.lean adds:
1. the finite 11-step certificate and head-window proof;
2. its arbitrary-tape lift using the existing bridgeAt;
3. a composition with the existing 35-step Type-C theorem;
4. a right-tail preservation lemma;
5. a source-side theorem for the complete M-4 BinDec checkpoint family, obtaining the required third blank from the right-side 000 guard.

The resulting source-prefix cost is 33+2+11=46 moves to state 4 at h+4.

## Next macro and current evidence boundary

The next candidate composition is now clear:
\`\`\`
Type-C 33 + two-zero setup 2 + state-1 bridge 11
  -> state 4 at h+4
  -> E_scan(m)
  -> two-zero setup 2
  -> state-1 d1-block scan(3n)
  -> q4Tail(29)
  -> S0 counted drain
  -> q4/S0 postlude
\`\`\`

A direct exact-table simulator was also run for (m,n)=(3,2),(5,3),(6,4). In all three cases, after the q4 tail the head-facing S0 word had the form
d0pow(n-1) ++ 1^(m+2) ++ [0,1,0,0] ++ tail,
and the right suffix was s0RightFacing(0). After the all-ones S0 drain and q4/S0 postlude, the next state-4 checkpoint had the type-A local window 00110000 and right-side shape
0^3 ++ 1^(m+3n+2) ++ 0^2 ++ 1^(3*2^(n-1)) ++ 0^4.

These are finite simulation observations, not universal theorems. The general source proof still needs to:
- compose the 46-step bridge with E_scan, the two-zero setup, d1-block scan and q4Tail_at;
- identify the q4-tail frame as the corresponding s0Config;
- apply s0Config_counted_drain_closed;
- establish the residual 1^(m+2) ++ 0100 guard and apply q4S0Postlude_at;
- prove the next type-A local window and right-tail recurrence for all admissible parameters.

Do not promote this note to results/ until that complete source composition is kernel-checked and its transitive axioms audited.
