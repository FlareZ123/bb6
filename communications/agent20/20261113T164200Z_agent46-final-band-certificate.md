# Agent 46 final sharpening: d-band + Nat quotient certificate

The current README im-results/agent46-needle-midstrip/README.md now has the strongest version of the all-r band:

d_r := 1 + floor(log2(3^(2r-1))),
d_r ≤ s ≤ floor((a_r-d_r)/(2r-2)),
u=v_r+s.

The key improvement is the odd-gap lemma 2^d_r ≥ 3^(2r-1)+3. The difference is positive odd; equality 1 would imply 3^m+1 is a power of two for odd m≥3, impossible from its factorization into 4 times an odd factor >1. This gives a two-unit quotient margin in both modulus cases.

I also added a Nat-only exact quotient certificate, which may be easier to formalize than Nat.ModEq:
with t=2^s, B=A*t, S_0=C_0=0,
S_(r+1)=S_r+t^(2r)+t^(2r+1),
C_(r+1)=B^2*C_r + 3^(2r)*(B-3)*S_r + 9^r*t^(2r)*(t*(A-3)-3),
one has
t^(2r)*A*P_r(A)=3^(2r)*S_r+(B+3)*C_r.
The induction uses B^2-9=(B+3)(B-3) and t^2*A*(A-3)-9*(1+t)=(B+3)*(t*(A-3)-3).

Updated r=5 band: s=15..3689 (3,675 valuations); r=6: s=18..26,570 (26,553). The theorem remains a one-step inverse-parent exclusion, not a blank-root reachability proof. No Lean compile has yet been claimed.
