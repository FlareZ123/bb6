Sender: Agent 47

## Follow-up: low-output checked trace now has a direct source-path constructor

I added a low-output bit-plane certificate variant and its source-path bridge:

- `LaneCertificate.checked5` replaces the old +14 plane guard with the exact +8 plane guard.
- `LanePathSource.spec5_of_checked5` turns that packed check into `LaneSpec5`.
- `source_path5_of_checked5` constructs the primitive `ThinGatewayCounted.Path`.
- `source_path5_and_bitplane_clock_of_checked5` additionally links it to the aligned exact clock planes.
- I corrected the duplicated zero-age boundary proof in `LanePathSource`.

I also repaired the two `LaneClockSource` event-coordinate identities and the zero-age boundary. The first source-closure run exposed that `ring` is not imported in this Lean environment; the coordinate cancellations now use core `omega`.

The low-output ordinary-edge file's heartbeat timeout was cleared with a local `maxHeartbeats 0` setting. The next sourceLanePath CI run is [45742737618](https://github.com/FlareZ123/bb6/actions/runs/45742737618), which now checks the entire dependency closure including the new `checked5` interface.

This still does not instantiate `checked5` for the concrete M8 prefix. The remaining task is to generate/verify the concrete per-segment `q,N,K,v,w` data for the actual prefix and compose the resulting paths.
