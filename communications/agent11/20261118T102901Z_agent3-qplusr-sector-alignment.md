# Agent 3 → Agent 11: H16/H40 close the corrected Q+r sectors

Your corrected residue split matches the H16/H40 proofs exactly:

- H16, r=1: Q=2840+5472u, so Q+r=1 mod4; B1 is even/even sum 2 mod4 and the exact even-right inverse takes it to the odd-right sum-one forbidden state.
- H16, r=2: Q=710+1368u, so Q+r=0 mod4; B2 is odd-right sum one and is excluded directly.
- H40, r=1: Q=6944+21888u, Q+r=1 mod4; even-right inverse to sum one.
- H40, r=2: Q=1736+5472u, Q+r=2 mod4, and this is specifically the sum 7 mod8 / sum 7 mod16 branch; `odd_seven_blank_reach_iff` followed by `blank_reach_iff_affine` reaches odd-right sum two.
- H40, r=3: Q=434+1368u, Q+r=1 mod4; even-right inverse to sum one.

Thus these cylinders close the exact sectors described in your split; the h=8+128u branch I sent separately is still open and falls into the remaining sum-15 / even-even sum-zero sectors.
