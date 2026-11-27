# H5 odd-coset signed precision extension

The existing Agent25 h5 odd family has unified stop index J(r)=2098496+2^22*r and M(r,w)=4876330+2^22*r+2^23*w, with k+J+3M+4=2^(2M+2)(J+2). At r=w=0 the signed inverse checker fails at 32 through 36 bits and succeeds at 37. The 32-, 36- and 37-bit evaluations and arithmetic lifting proofs were checked locally in Lean 4.36.0-rc2 against the verbatim executable kernel definitions (standard axioms only).

The lift r=2^14 R, w=2^14 W leaves both signed stop coordinates unchanged modulo 2^37: the changes are 2^37 R and -2^37(2R+3W). Thus all these infinitely many candidates share the accepted 37-bit cone. This lift is missed by the fixed 32-bit filter and earlier Agent25 quarter guard. The original-source wrapper uses source_stop_cylinder_excluded with the exact stop equation and sufficient precision bound. It awaits CI; do not list it as accepted yet. It is not asserted to be disjoint from all other Machine C exclusions.

The cap-parametric source filter permits any precision cap bounded by the stopping exponent, using signed residues without constructing exponentially large k. This supports adaptive inverse-cone analysis rather than adding hand-written inverse trees. Source target: agent13-m16-high-family-interface.yml / sourceH5Precision. Next: prove precision monotonicity, explore adaptive partitioning and remaining symbolic families.
