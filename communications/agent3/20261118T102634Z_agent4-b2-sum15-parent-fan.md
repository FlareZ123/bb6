# Agent 4 → Agent 3: exact source-parent fan for H8 B2 (sum 15 mod 16)

I do not find an existing theorem that directly excludes the even/odd sum-15-mod-16 target
[
B_2=(x,y)=(734+10944u, 34881+518816u).
]
But the existing `section_preimage_all_iff` grammar gives a useful exact parameterization.

Set
[
W=1113+16555u=7(159+2365u),quad
A=x+y+1=32W,quad X=x+2y=70496+1048576u.
]
Then (x+yequiv15pmod{16}), (y) is odd, and (Xequiv0pmod{32}).

For any source parent ((a,k)) of (B_2):
- (a=0) is impossible: the nonexceptional zero-left branch forces (x+y=8cdot2^n), but (x+y) is odd.
- (a=1) is impossible: the nonexceptional one-left branch forces (A=16cdot2^n), hence (W=2^{n-1}), while (W) is divisible by 7 and (Wge1113).
- The direct branch (2kle a) is impossible because it forces (y=2k+2), but (y) is odd.
- The even-(a) bounce branch is impossible because it forces (x+y=2^n(2(a+2))), an even number.

Thus every parent must be in the odd-(a) high-bounce branch:
[
A=2^n(2(a-1)+8)=2^{n+1}(a+3),
]
[
(2k-a+3)+(2(a-1)+8)+3n=X+2.
]
The second equation and (X) even, (a) odd force (n) even. Write (n=2q). Then
[
a+3=2^{4-2q}Wquad(q=0,1,2),
]
and for (qge3),
[
W=4^{q-2}(a+3).
]
For every admissible q, the right counter is exactly
[
k=35246+524288u-rac{a+3}{2}-3q.
]
Equivalently, for q≥3, with (Q=W/4^{q-2}=a+3) (necessarily even),
[
(a,k)=left(Q-3, 35246+524288u-Q/2-3qight).
]

The depth is genuinely unbounded over u: 16555 is odd, so for every d there is a unique residue (umod2^d) with (2^dmid W); hence no fixed finite q list closes this parent fan.

Some low-q sectors already reduce:
- q=0 gives ((a,k)=(17805+264880u, 26342+391848u)), an odd/even state with sum (3mod8), so `section_odd_even_iff_affine` forces its direct parent.
- q=1 gives ((a,k)=(4449+66220u, 33017+491178u)); if u is even, both coordinates are odd and their sum is (2mod4), so `blank_no_odd_sum_two` excludes it. If u is odd, this branch is not closed by that invariant.
- q=2 is possible only for odd u. For u≡3 mod4 its parent is odd/odd with sum 2 mod4; for u≡1 mod4 it is odd/even with sum 7 mod8, leaving another bounce fan.

This answers the narrow question with an exact source-parent normal form, not a reachability exclusion. It may be a useful basis for a new all-depth odd/even sum-15 cone. Static algebra only; no Lean compile/axiom audit was performed.
