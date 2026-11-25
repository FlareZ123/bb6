# Constant F-run lengths cannot support an infinite signed path

This is a structural reduction for the compressed signed inverse system. It is not a proof that every mixed path terminates: it rules out only paths whose F-run lengths are eventually constant.

## Setup

Use the compressed blocks
- F: (u,D) maps to (u/2,D+3u+3);
- EF: (u,D) maps to (u+(D+8)/8,D/4+4);
- SF: (u,D) maps to (u+(D+20)/8,D/4-1).

In the admissible region, u>0, D>=2, and D!=4. The existing signed-drift theorem proves that an infinite path contains infinitely many standalone F blocks and infinitely many paired blocks. The F-run parity theorem proves that every F-run followed by a pair has even length. The refined endpoint tables show that a run of length m congruent to 2 mod 4 preserves the pair type (E or S), while a run congruent to 0 mod 4 switches it.

Let a pair input be (v,d), and let (w,e) be the endpoint after that pair followed by m F blocks. Define the integer defect

    H_m(x,y) = y - 8(2^m x - x).

The endpoint identities are formally checked in Branch13_15.lean, in ef_macro_defect_components and sf_macro_defect. They give:

- EF followed by m F blocks:
  
      H_m(w,e) = 2(w-v)+2+3m
      H_m(v,d) = 8*2^m(w-v)-8

- SF followed by m F blocks:
  
      H_m(w,e) = 2(w-v)-6+3m
      H_m(v,d) = 8*2^m(w-v)-20

With M=2^(m+2)=4*2^m, these are the affine recurrences

    M H_(n+1) = H_n + A_E,    A_E=(2+3m)M+8

for EF, and

    M H_(n+1) = H_n + A_S,    A_S=(3m-6)M+20

for SF.

## No eventually constant run length

Suppose the F-run length is eventually one fixed even integer m.

### Case 1: m congruent to 2 mod 4

The pair type is eventually constant.

If it is E, the recurrence has constant shift A_E; if it is S, it has constant shift A_S. For either recurrence,

    (M-1)H_0-A = M^n((M-1)H_n-A)

for every n>=0. The fixed integer on the left is therefore divisible by arbitrarily large powers of M>1, so it must be zero. Hence M-1 divides A.

But

    A_E = 10+3m (mod M-1)
    A_S = 14+3m (mod M-1).

For m=2, M-1=15, and the respective residues are 16 (congruent to 1 mod 15) and 20 (congruent to 5 mod 15). For m>=6, both 10+3m and 14+3m are strictly between 0 and M-1=2^(m+2)-1. Thus neither shift is divisible by M-1, a contradiction.

### Case 2: m congruent to 0 mod 4

The pair types alternate.

For m=0, M=4, A_E=16, and A_S=-4. Over an E,S pair of macros the two-step shift is A_E+M*A_S=0, forcing the defect H_0=D to be zero on an infinite orbit. Over an S,E pair it is A_S+M*A_E=60, forcing 15D=60, hence D=4. Both possibilities are excluded by D>=2 and D!=4.

Now let m>=4, so M=2^(m+2)>=64. The two-step shifts are

    A_ES = A_E + M*A_S
         = (3m-6)M^2 + (3m+22)M + 8

    A_SE = A_S + M*A_E
         = (3m+2)M^2 + (3m+2)M + 20.

Modulo M^2-1, their remainders are respectively

    r_ES = (3m+2) + (3m+22)M

    r_SE = (3m+22) + (3m+2)M.

For m=4, M=64, these are 2190 and 930, both strictly between 0 and 4095=M^2-1. For m>=5, induction from m=5 gives 3m+22<=M/2 and 3m+2<=M/4. Consequently,

    0 < r_ES <= M^2/2 + M/4 < M^2-1

    0 < r_SE <= M^2/4 + M/2 < M^2-1.

Neither two-step shift is divisible by M^2-1. The same iterated-divisibility argument applied to the two-step recurrence forces that divisibility, a contradiction.

Therefore no infinite signed path can have an eventually constant F-run length.

## Consequence and remaining gap

A hypothetical infinite path must use infinitely many distinct even F-run lengths; it cannot settle into a constant-length macro regime, whether the pair type stays fixed or alternates.

This does not exclude paths with a genuinely varying run-length sequence. Proving that such a sequence cannot occur—or finding a well-founded descent that covers it—is still the mixed-path termination problem. The result applies to the branch-13 and branch-15 families as well as the branch-29 feeder line; it does not itself close any of those families or establish a BB(6) value.
