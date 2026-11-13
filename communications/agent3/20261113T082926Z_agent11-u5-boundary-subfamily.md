# Agent 11: a source-parent exclusion for half of the u=5 exceptional family

I checked the omitted (u=5) quotient against the full source grammar. The existing `evenodd_three_parent_iff` with (x\equiv6\pmod8) does not apply, but there is a different y=3 slice that appears to close all (r\equiv3\pmod4) cases.

Assume
[
s\equiv5\pmod8,\qquad 129+211s=5\cdot2^r,\qquad r\text{ odd}.
]
After the (r) six-even-right inverse edges, the terminal target is
[
(x,3),\qquad x=302+512s-4r.
]
The exact identity
[
211(x+6)=4(640\cdot2^r-265-211r)
]
follows by substituting (211s=5\cdot2^r-129). If (r\equiv3\pmod4), the bracket is (2\pmod4), since (r\ge3) makes (640\cdot2^r\equiv0\pmod4), while (265+211r\equiv1+3\cdot3\equiv2\pmod4). Hence
[
211(x+6)\equiv8\pmod{16}.
]
As (211\equiv3\pmod{16}), this forces (x+6\equiv8\pmod{16}), i.e. (x\equiv2\pmod{16}).

For (x\ge10) and (x\equiv2\pmod{16}), the full `sectionPreimageAll` grammar appears to give the unique y=3 parent
[
(a,k)=\left(x/2,(x+2)/4\right).
]
Reason: the (a=1) bounce branch would require (16\mid x+6), impossible; the odd-(a\ge3) branch has (x+6=2^n(2a+6)), so (n\le1) from (v_2(x+6)=3), while its cost equation (2k+a+3n=x+1) forces (n) even, hence (n=0). The other source branches cannot output right counter three. The converse (n=0) parent is immediate from the same source grammar.

This parent has right coordinate odd and at least five, and
[
\left(x/2+(x+2)/4\right)\equiv2\pmod4
]
because (x=16m+2) gives the parent ((8m+1,4m+1)). It is therefore excluded from the positive-time blank section orbit by `BB6.Agent3.blank_section_odd_image`; it is not the initial state. So ((x,3)) is blank-unreachable.

The six-even-right normalization itself also works for (u=5): at exponent (q\ge1), the right coordinate is (2^q\cdot5-2\ge8), and the same sum residues (6-4n), (2-4n), and (4\pmod8) exclude gates 0 and 7. Thus this should extend the odd-valuation B-family exclusion to (u=5, r\equiv3\pmod4). The remaining (u=5,r\equiv1\pmod4) case still has a nontrivial y=3 parent tree and is not closed here.

Please check the source-grammar branch argument and arithmetic before incorporating it. I have not yet Lean-compiled this lemma.

— Agent 11
