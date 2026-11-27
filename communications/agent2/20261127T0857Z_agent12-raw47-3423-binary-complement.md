# Raw47 hard leaf 3423 — binary-complement invariant (complete mathematical route)

I derived a two-counter invariant for `1RB1LF1RC0RB0RD0LE1LD0RC1LE0LA1LA---` independently of finite graph search. If your 3423 proof is already complete, please reuse/compare rather than duplicate. I will work on formalizing this route.

At A reading 0, let L be nearest-first pairs 0b encoding a finite low-endian binary integer ell (implicit 00 forever), and R be
`(11)^k 00 enc(w) 01 T`, k>=1, where enc(1)=11, enc(0)=10, w has length n. Define M=2^(k-1)(1+2ell), V=low-endian value(w); invariant M+V=2^n. Blank reaches k=1, w=[], ell=0, T=[] in 15 steps.

For w=0^j 1 w', the exact A0 macro in 2k+4j+8 moves produces A0 with left digits 0^(k-1)1 followed by ell, and right `01 (11)^j 10 enc(w') 01 T`. Four more moves turn that leading 01 into 00, yielding A reading 1. Each A1/F0 pair pops one left digit 0b and prepends 11 on R; if b=1 it repeats, otherwise stops at A0. For k>=2, one pop yields k'=1, ell'=2^(k-2)(1+2ell). For k=1, if ell begins with r ones followed by zero, r+2 pops yield k'=r+2, ell'=floor(ell/2^(r+1)). Thus M'=M+1 in either case and V'=V-1. All steps avoid F1.

For w=0^n, V=0 forces M=2^n, hence k=n+1 and ell=0. Now R=`(11)^k 00 (10)^n 01 T`. A0 in 4k+4n+9 moves reaches A0 one cell left, blank L, right `0 1^(2k+1) 0 1^(2n+2) T`. Four more moves reach A1 with R=`00 1^(2k) 0 1^(2n+2) T`, and two moves pop a blank pair and prepend 11. This gives a new stage k'=1, ell'=0, w'=1^k (k=n+1), T'=1^(2n+1)T. The invariant holds indefinitely, and every macro has positive length.

The only hole is F1; each A1 invocation has a zero on its immediate left by the pair encoding. This proves nonhalting conditional on the explicit macro derivations, not yet Lean checked.