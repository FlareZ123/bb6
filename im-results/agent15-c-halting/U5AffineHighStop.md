# U5 M8 residual: unified affine exclusion at the original high stop

For natural w,s,m with 211s+129=5*2^(201+3360w) and 32s=32+840w+m, proposed theorem high_stop_excluded excludes blank reachability of the original high stop (2(39+64s)+3,3(39+64s)+7) whenever wFilter w is true.

Local RC2 checked arithmetic and proof bodies against signature stubs, and evaluated exact copied checker definitions. Original-source CI pending.

Put t=m/8. The exact residual identity 211t+1360+22155w=20*2^(201+3360w) implies t=60+105n by reduction modulo 21 and 5. Since 22155=211*105, reduction modulo 65536 gives (n+w)%65536=16180 (inverse 57635 of 22155). Thus n=b+65536j for b=(16180+65536-w%65536)%65536. The X-parent (44t-1,42t-1) is a nonnegative affine ray in j. Agent13's complete inverse-cone checker at fuel 24 excludes all its points if true. Fuel bounds certificate depth, not execution time.

Executable census: 54715/65536 (83.4885%) accepted residue classes. Counts by w mod 8, out of 8192 each: [8192,4365,8192,8192,8192,4331,8192,5059]. Even and w=3 mod 8 families were previously excluded. Do not count all accepted classes as new. Complement is unresolved by this checker, not necessarily reachable.

Source chain: exact y=3 parent fan; q=0 via two unique source parents to X, q=1 violates odd-image obstruction, q>=2 contradicts odd m+1. Six-even-right chain lifts to B_s. A_s has two parents: L_s excluded by s=5 mod8, B_s excluded above. First-two-reach lifts to original high stop. See [U5AffineHighStop.lean](U5AffineHighStop.lean). The universal implication is separate from the executable census; no claim of a complete Machine C or BB(6) solution.
