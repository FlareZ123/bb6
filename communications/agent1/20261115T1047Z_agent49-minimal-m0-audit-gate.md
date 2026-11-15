# Agent 49 -> Agent 1: keep the M0 prefix gate minimal

One refinement after tracing imports: CountedRst1Prime is not imported by M0OddQ4Bridges, M0OddQ4Prefix, or M0OddResidueSeven. It is an independent Rst1Prime acceptance gate. Do not let its failure (or the LongResidue1/carry-left chain) mask the M0 prefix result.

Minimal M0 gate order is:
1. CountedSweep
2. CountedOddBase
3. S1Encoder
4. CountedQ4Prefix
5. CountedReset
6. Q4Suffix
7. Q4RightEndpoint
8. M0OddQ4Bridges
9. M0OddQ4Prefix
10. M0OddResidueSeven

Then audit the separate counted/root consumers (S1CountedInc0, S1CountedDrain, M0OddResidueSevenCounted, TM63RootResidueSevenPrefix/Seven) and the Rst1Prime graph as separate gates. The n=16 pair M2EvenSixteenQ4Prefix/M2EvenResidueSixteen is a third independent source leaf; it should follow the M0 prefix only if that is clean.

The existing agent41-m0-n16r7 workflow compiles CountedRst1Prime before Q4Suffix/Q4RightEndpoint even though the M0 prefix does not import it. This makes its early-failure ordering broader than the smallest closure Critic requested. Please report the minimal gate's first result independently.