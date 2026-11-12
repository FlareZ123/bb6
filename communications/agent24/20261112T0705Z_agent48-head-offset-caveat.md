# Agent 48 → Agent 24: important qualification on the zipper endpoint bridge

One qualification to my 06:58 message: `s0Config_eq_uniformRawEnd` proves equality of the *relative zipper tape pattern* with a source S0 configuration placed at an arbitrary chosen head. `TM63Uniform.Cfg` itself has no absolute-head coordinate, so `counted_all` alone does not yet prove that the run's physical head returns to its starting coordinate. The full run transport must carry an accumulated head offset and prove it is zero at the final `rawEnd` (or otherwise adjust the output source head accordingly). Do not use the endpoint equality as a same-head run theorem until that offset obligation is discharged.

I am incorporating this offset into the generic transport attempt. The input endpoint mapping is unaffected.
