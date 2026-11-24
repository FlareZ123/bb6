# Radix-four convolution: logarithmic residual along strict half-step histories

[Q0DigitConvolution.lean](Q0DigitConvolution.lean) proves the arithmetic theory and [Q0DigitConvolutionSource.lean](Q0DigitConvolutionSource.lean) connects it to the exact history identities of Q0SignedCarry. This removes the dependence of the height carry's size on the near-power rank offset, at arbitrary ranks. It does not exclude a q0 parameter or bound the full history-state count polynomially.

Let h_j be the most recent binary choices, newest first; V_0=0, V_(j+1)=4 V_j+h_j. For little-endian radix-four rank digits a_j, set P=sum a_j 4^j, S=sum a_j, F=sum a_j V_j. Write Y=F+e. For a strict k-step history ending at P<=4^k with at most k+1 rank digits,

    M F <= P V_k,
    3 P V_k <= 3 M F + M S,
    0 <= e, 3e <= S+3 <= 3(k+2),

where M=4^k. The first inequalities follow from 0<=V_k-4^(k-j)V_j<4^(k-j)/3. The residual bound combines them with the exact signed history formula M Y=y+P V_k+E and its bounds -M<E, 15E<13M, 0<3y<P. The source adapter proves residual_of_history and the equality between V_k and the original chronological digits. No near-power assumption is needed.

## Exact updates

For the half-step bit d, rank increment l=len(s,d), height offset c=off(s,d), shifted history h'=push(d,h), and digit addition a_j+t_j=b_j+4 t_(j+1), t_0=l, terminal carry zero, let B=sum a_j h'_j, C=sum t_(j+1) h'_j. The identities are

    4 F(h',a)+B=F(h,a)+dP,
    F(h',b)=F(h',a)+C,
    S(b)+3 sum t_(j+1)=S(a)+l,
    4e'+4C=e+c+B.

The last equation is equivalent to the original height equation 4Y'=Y+dP+c, not merely necessary. The radix addition reconstructs the correct rank P'=P+l. For g=S-3e, also

    4g'=g+3(S-B)+4l-3c-12(sum t_(j+1)-C).

Rank and height phase parity and strict cone tests still apply. For A, c is 0 or 12; for B, c is 0 or 4. The complement relation uses the same small carry digits. Width can be fixed larger than all ranks in a window. Leading rank zeros are harmless. In particular this is a finite-memory recurrence of length logarithmic in rank, with small integer residuals, but the retained binary history has exponentially many possible words.

## Status and intended use

The complete arithmetic core and source adapter compiled locally in Lean 4.36.0-rc2, using actual verbatim relevant HalfStep/Trace and Q0SignedCarry declarations and proofs as the dependency slice. All exported theorems use standard axioms only. The full untouched repository dependency closure was not rebuilt. The compiled local blobs were e9353a309d07ca1b1600631b9568d755efdf0062 and 82e61efd4709ec22f5e3576b40999e656012ea87.

The remaining target is an all-scale obstruction for the exact rank/history transducer or a sufficiently strong near-power crossing criterion. Digit carry chains expose delayed taps at multiple scales; a naive independent-bit projection discards exactly those correlations. See [Q0HalfWindow.md](Q0HalfWindow.md) for the wide first-crossing reduction and its counterexample to a short-window conjecture. The convolution alone does not decide #429 or BB(6).
