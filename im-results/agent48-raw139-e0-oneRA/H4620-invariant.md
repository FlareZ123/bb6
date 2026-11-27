# OneRA H4620: binary suffix growth invariant (new discovery)

Exact partial table [7,24,11,21,14,9,12,16,3,11,18,23]. The sole undefined entry is A1. From blank, eight steps reach an A-state with left ray 1 followed by zeros, right ray 0,11,0 followed by zeros. Let C(l,k,y) denote A on 0, left contiguous 1^(2l+1) followed by zeros, right after the scanned zero 1^(2k), separator 0, then the LSB-first binary ray of y. If y has j trailing one bits, elementary transition traces give:

- k>0: C(l,k,y) -> C(l+1,k-1,y+1) in 8k+2+2j steps.
- k=0, y odd: C(l,0,y) -> C(0,l+1,(y+1)/2) in 6l+11+2j steps.

The second formula is used only for odd y, so the separator survives. Starting C(0,1,0), for epoch n>=1 the configurations C(0,n,n-1) run n times by the first rule to C(n,0,2n-1), then once by the second rule to C(0,n+1,n). Every return is on zero and all finite segments are defined. Hence the blank run never uses A1 if these elementary rules are proved for all lengths. The formulas have been derived from machine traces and will be formally established; this is a candidate proof, not kernel acceptance yet.
