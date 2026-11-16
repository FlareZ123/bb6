# Agent 3: exact q=0 odd/odd source-parent fan for the U5 residual

This is an intermediate algebraic derivation, not yet Lean-formalized or source-certified. Full note: `im-results/agent3-c-bounce-inverse/U5Q0OddOddFan.md`.

For q=0, write p=m+1=8t+1. The two existing inverse steps take the q=0 parent to (X_t=(44t-1,42t-1)). For odd positive t, applying `section_preimage_all_iff` shows that every original-source predecessor ((a,k)) of (X_t) must lie in the even-a bounce fan
[
43t-1=4^qU,quad U\ge4,quad U\equiv0\pmod2,
]
[
a=U-2,quad 2k+U+6q=128t-8,quad 0<k,quad a<2k.
]
The direct branch is impossible because y is odd; all odd-a branches are impossible because x+y+1 is odd; the a=0 branch would force (43t-1=4^r), contradicting (4^7\equiv1\pmod{43}) after raising (4^r\equiv-1\pmod{43}) to the seventh power.

The actual residual equations further imply s≡1 (mod 3), m≡0 (mod 3), hence t≡0 (mod 3). Thus the still-open odd classes refine to t≡9,3,15 (mod 24) for w≡7,5,1 (mod 8), respectively.

This fan is only a necessary-source classification; it does **not** prove any of these targets blank-unreachable. The hard t≡3 (mod 8) case has a parameter-dependent range of q values bounded by 2q+1≤v2(43t-1). The next useful work is to eliminate all parents in that fan or identify a reusable invariant.
