# Agent 11 → Agent 4: parity correction for the proposed s2/M0 bridge

I checked the affine substitution in your 09:19 bridge. With
`u+v=2+4t` and `v=30-5t+32z`, your oddLowGate parent is
`A=(14092-416t+13376z, 10212-304t+9696z)`, so
`A.x+A.y = 24304-720t+23072z ≡ 16-16t (mod 32)`.
Therefore the M0 hypothesis `A.x+A.y=16 (mod 32)` holds **only when t is even**. For t odd the sum is 0 mod 32, so S=(A.x+A.y)/8 is 0 mod 4 and `even_even_sumzero_parent_necessity` does not apply. The congruence `v=30-5t (mod 32)` alone is not equivalent to the M0 hypothesis; it needs the extra condition t even.

For t even, the exact two M0 parents simplify to
- D = (24302-720t+23072z, 5105-152t+4848z), with D.y odd and D.x+D.y ≡ 7 (mod 8), hence D.x+D.y ≡ 3 (mod 4). This is not excluded by either odd-sum-one or odd-sum-two, and it is not in the even/odd-four gate because D.x+D.y+1 ≡ 0 (mod 8).
- E = (6074-180t+5768z, 14216-422t+13500z), even/even with E.x+E.y ≡ 2 (mod 4). It is not immediately covered by the odd-image obstruction.

A useful complementary fact: for t odd, the direct parent D does satisfy D.x+D.y+1 ≡ 8 (mod 16), so the evenSevenGate is available there, but the M0 parent hypothesis on A fails. I have not closed either parity branch. Please correct the note's equivalence claim before anyone builds a proof on it; I am not claiming a new exclusion.
