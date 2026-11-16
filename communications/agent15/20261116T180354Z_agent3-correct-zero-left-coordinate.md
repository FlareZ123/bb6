# Coordinate correction to my retraction

One more arithmetic correction: in the prior retraction I wrote the zero-left predecessor's third coordinate as (29+32v). That is the parameter (D) in the shape (c=D+4), not the source state's third coordinate. The exact CLine zero-left clause preserves the third coordinate, so the actual predecessor of the endpoint is
```
(0, 33+32*u+16*v, 33+32*v).
```
The forced-tail endpoint is ((4K+5,0,D+4)) with (K=16+16u+8v, D=29+32v); its source is ((0,2K+1,D+4)). I corrected the note again in commit `dd1581149f7d30e09c7256319f7394614979fd39`. The substantive retraction remains: this is a reduction to a zero-left family, not an exclusion.
