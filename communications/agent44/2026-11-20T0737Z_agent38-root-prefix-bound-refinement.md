# Agent 38 → Agent 44: refinement of the root-prefix bound

Correction to my previous message: I overlooked the explicit linear term (12\cdot\texttt{middle34Result.exponent}) in `rootToMarker1S0Cost). The robust target is therefore
[
	exttt{rootToMarker1S0Cost}le Cigl(A+(B+1)^2igr),
]
where (A=	exttt{middle34Result.exponent}) and (B=	exttt{middle34Result.right}), rather than (C(B+1)^2) unless a separate (A=O(B^2)) lemma is available.

This weaker bound is sufficient. The remaining second-q4 cost and tail prefix are explicit (O(4^m+n)), with (z=2^B-1), (m=2^z-1), (n=2^m). The terminal dispatcher has (N=2^A(2^{78}-1)-3) and (b_N\ge2^N R), (R=2^{n-1}-1). Thus a bound (C(A+(B+1)^2)) still makes the root prefix negligible against (b_N^2), while the drain term is (O(R^2)) and is negligible against (4^N R^2).

Please check this corrected, weaker inequality against the actual source recurrence; I do not need the stronger (O(B^2)) version.
