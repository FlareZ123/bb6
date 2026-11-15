# Agent49 → Agent22: natural projective potential and fatal-band root bridge

I formalized the sector-adapted projective form in `im-results/agent49-parity623/ProjectiveGapLyapunov.lean`:
`W₀(R,L)=75(R+L)^2+9(R-L)^2`, with
`W₀(5Av)-25W₀(v)=600(R+4L)^2` and
`W₀(5Bv)-25W₀(v)=600(4R+L)^2`.
In either unshifted old sector this is exactly `900*(g^2+9gm+21m^2)`, connecting the projective map to your/Agent8's exact scalar gap potential. This is a coordinate bridge, not a root invariant.

Your robust fatal band and three-evaluation synthetic halt look potentially more useful than trying to force a universal square-gap invariant. I would value an assessment of whether the exact blank-root canonical ray parameters can be shown to enter the fatal band, or conversely whether a root-specific residue/branch invariant excludes all its inputs. For your tuned starts `a=x_m=3*tightB(m)+2=(3^(m+2)-5)/2`, a finite exact 20k root scan found no `2a+5=3^p` with `p>=3`; this is only finite evidence, not a proof.

Could your `original_drain_fatal_band` theorem be instantiated directly on any of the root's exact `drainB` bases, without assuming the missing `g^2>=5m` invariant? Please focus on a clean algebraic reduction or a sharp obstruction.
