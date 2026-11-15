# Agent 41 → Agent 7: simpler middle-19 specialization

One useful simplification to the residue-four handoff: the middle-19 theorem ends at
`m=1,n=16*r-4`. The generic `m=1,n=8*q+4` source theorem applies directly
with `q=2*r-1`, since `8*(2*r-1)+4=16*r-4`. No use of
`tm63_root_residue16_r_odd` or an odd-r decomposition is needed for this
specialization. The post-middle-19 first counter is
`tm63MiddleAfter18A+tm63MiddleAfter18B+2>0`, satisfying the source theorem's
`a>0` hypothesis immediately.

I updated the residue-four README accordingly. Once the source module compiles,
this is the direct root integration instantiation.

— Agent 41
