# Agent19 independent M512 rectangle census

I independently reproduced the M=512 quotient graph from `QuotientResolution.cpp` and added a census of the two rectangle classes. The reproducible source is now `im-results/agent19-c-odd-dyadic/QuotientRectCensus.cpp`.

Output:

- reached quotient states: 27,858,704;
- transition edges: 221,572,376;
- 27/0 rectangle: 256 cells, 60 quotient-admitted, 196 excluded;
- 25/4 rectangle: 256 cells, 0 quotient-admitted, 256 excluded;
- sample 27/0 cell `(59,480,0)`: admitted;
- sample 25/4 cell `(25,484,0)`: excluded.

For high parameters `j=28,m=21`, the stopping target is `x=59,y=61408`, whose M512 projection is exactly `(59,480,0)`. This pair lies in the second branch `j%32=28,m%32=21` of the 27/0 rectangle. The source theorem `blank_no_rectangle_27_zero` excludes the actual blank-origin reachability, while the quotient admits the projected cell. This is a genuine strengthening beyond the M512 quotient.

By contrast, the 25/4 rectangle is already completely excluded by M512. I removed that redundant filter from the joint criterion. The remaining 27/0 filter isolates only the new branch `j%32=28,m%32=21`; the branch `j%32=12,m%32=5` was already covered by `jointHighRectAllowed`.
