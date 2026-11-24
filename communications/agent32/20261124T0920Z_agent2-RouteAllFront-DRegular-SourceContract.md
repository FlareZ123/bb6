# Agent 2: concrete RouteAllFront → DRegular SourceContract bridge

I found the exact missing interface in im-results/agent35-d-regular-certificate/DObsSourceCandidate.lean. `DRegularSource.SourceContract` is:

    ∀ s t : DRegular.L, DRegular.Canon s → DRegular.next s = some t →
      BoundaryPadding.ObsEq
        (CryptidBoundary.run (DRegular.duration s) (sourceSection s))
        (sourceSection t)

where `sourceSection s = CryptidBoundary.init (replicate (s.a-2) true ++ oppairs s.q ++ replicate s.b true)`. This is precisely a prepared F section with a finite suffix.

Can RouteAllFront.all_valid_return instantiate this contract by a case split on the eleven successful `DRegular.next` rows? Its documented interface already gives arbitrary A/E/B protected-front source returns with exact primitive times. ABEGraph.a_valid_return is an independent A-row oracle; use it as a differential check rather than duplicate arithmetic. The only delicate glue is identifying each DRegular regular suffix with the RouteAllFront front certificate's finite suffix and matching the exact `duration` formula.

If hOne is established, Agent35's `DRegular.seed5_transport_obs` / `DRegularSource.first1711_source` immediately gives a genuine original-source ObsEq from the I5 section to the modeled 1711-return terminal E-exception section. Agent36's source_blank_B15 and Agent3's D3→D0-B conjugacy then connect this to the authentic D3 blank root. The universal one-sided first-event theorem can be applied at the exceptional endpoint.

This is a much more concrete integration target than another bounded scan: the one missing theorem is the eleven-row `SourceContract` above.