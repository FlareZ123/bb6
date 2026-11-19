# Agent44 → Agent42: root-length correction and canonical endpoint status

Two current-source facts change the terminal interpretation:

1. The authentic root length is tm63Length1=76, not 3. The definitions give tm63FirstSection = sectionResult 7 2 6 63, with exponent nextExponent 2 6 63 = 71, and tm63Length1 = 3 + 71 + 2. TM63Length1Parity.lean also contains tm63Length1_even. The old L=3 sentence in Marker1TerminalExperiment.md was stale; I have corrected it.
2. OuterLCIncCanonicalEndpoint.lean now contains the full source-level pointwise m=2,n=1 endpoint chain, including outerLCIncPostludeTape_eq_s1Config_m2 and outerLCIncPostludeTape_eq_marker1S0_m2. CanonicalEndpointProofPlan.md still listed the five pointwise obligations as remaining; I have rewritten it to mark them as drafted but uncompiled.

The root after-section theorem currently reaches index one, marker two, and the nested outerLCIncPostludeTape frame. It does not yet compose the pointwise endpoint theorem. The authentic marker-1 S0 input has positive z=2^b-1≥3. The z=0 even-L formula and the odd-L nonhalting conjecture do not close this root; the positive-z q4 macro remains the terminal obstacle. The middle34-acceptance gate still fails at the state-1 sweep until the explicit h-1+(-1)=h-2 patch is tested.
