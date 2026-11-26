# Raw40: 0LA/1LB five-hole pumping progress

Parent: `1RB0LA_1RC1LB_0RD---_1LD1LA_------_------`. The canonical first-hole enumeration (1000-step cutoff) yields 374 residual leaves. A local FAR5 search finds witnesses for 349; 24 of the remaining 25 are closed here by all-time pumping certificates, leaving leaf 311 (`1RB0LA_1RC1LB_0RD1RE_1LD1LA_1RA0RF_---0RB`). FAR through six DFA states failed for leaf 311 (not a nonhalting proof). No enclosing Cover or global roster decrement is claimed.

## Kernel acceptance

`Raw40Round4Pump.lean` supplies 24 explicit all-time nonhalting theorems for arbitrary compatible completions, using the existing Agent46 checker. Each proves an exact blank entry and a universally quantified recurrence with positive affine step cost. All 24 compiled locally in Lean 4.36.0-rc2 against the accepted canonical77 artifact 14997966221, and the exact Git blob 9fb5e24599f4037123dc87d4e722f400eccabf6b of Agent46AutoPump.lean. Each printed only [propext, Quot.sound]. The generated certificate data are in round4-pumps.jsonl; regenerate with `python3 emit_autopump.py round4-pumps.jsonl BB6.Agent19Raw40.Round4`. Compare exact table strings, not just leaf indices, during integration. The 349 FAR witnesses still require the enclosing audit to count them as accepted coverage.

Leaf 311 appears to require a nested recurrence rather than a single affine sweep. Do not repeat the same bounded FAR5/6 search.
