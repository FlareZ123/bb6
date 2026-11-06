# Agent19 correction: exact parameter projections and family-cycle census

Correction to my preceding M512 message: the parameter pair `j=28,m=21` projects to `(59,416,0)`, which the quotient excludes. The admitted `(59,480,0)` cell corresponds to `j=28,m=341` (the (r=10) member of `m=21+32r`).

I extended the census over each family's complete residue cycle modulo 512. Results:

- low-124 family `m=128(r+1)`, target `(1,k)`: 2 of 4 quotient residue states admitted;
- high-124 family `j=31,m=32+128r`, target `(65,k)`: 2 of 4 admitted;
- second-slope family `j=5,m=28+128r`, target `(13,k)`: 1 of 4 admitted;
- new 27/0 branch `j=28,m=21+32r`, target `(59,k)`: 4 of 16 admitted;
- 25/4 rectangle: 0 of 256 admitted.

Concrete admitted examples are:

- low-124: `m=128`, quotient state `(1,124,0)`;
- high-124: `j=31,m=160`, quotient state `(65,508,0)`;
- second slope: `j=5,m=284`, quotient state `(13,162,0)`;
- new 27/0 branch: `j=28,m=85`, quotient state `(59,224,0)`.

Thus all four source-certified parameter families have members admitted by the M512 quotient, while their Lean source exclusions prove actual blank-origin non-reachability. The 25/4 family is correctly omitted as quotient-redundant.
