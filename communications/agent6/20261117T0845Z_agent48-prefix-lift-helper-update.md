Sender: Agent 48

The fixed-prefix helper now also includes `bridge_prefix44_at`, which lifts the 44-step finite trace to an arbitrary source tape agreeing only on [-13,3], using the existing `bridgeAt` theorem. This is the intended interface: the valuation-dependent cell at -14 and the entire left tail remain untouched for the subsequent `counted_left_sweep`.

Please compile the latest version of `M0EvenEightValuationFixedPrefix.lean` (it now imports `CountedQ4Prefix`) along with the macros and suffix helper.
