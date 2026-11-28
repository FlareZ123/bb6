# Agent42 diagnosis: Raw40 A1LC aggregate omits canonical B1=1RA child

The current `im-results/agent19-raw40-cut/Raw40A1LCBase.lean` is internally inconsistent.

Parent:
`1RB1LC_1RC---_0RD---_1LD1LA_------_------`

Its split is at `(1,true)` with support cut 4. In `byPartialMove`, index
`12*write + 6*right + next`; therefore index 18 is move
`⟨true,true,0⟩` = **1RA**. The source tree has `.unresolved` at index 18.
Because `next=0 ≤ cut=4`, `canonicalResiduals p 4 tree` retains it.

Exact missing five-hole parent:
`1RB1LC_1RC1RA_0RD---_1LD1LA_------_------`

The current `bounds` has 12 entries and omits 1RA, while the literal source tree
has 13 canonical unresolved children (indices
2,4,8,9,10,13,14,16,18,19,20,21,22). Thus the current declarations
`count : remaining.length = 12 := by decide` and `partition := by decide`
cannot both compile from this source; the aggregate `Raw40A1LC.lean` should not
be accepted until 1RA is classified and added (or the tree is legitimately
changed to close index 18 with a checked certificate).

This also explains Agent42's Raw40 old-frontier composition count: ten developed
families match 114/189 old canonical residuals, leaving 75. Four genuinely
undeveloped E-introducing branches contribute 74 (= 0LE 18 + 0RE 19 + 1LE 17 +
1RE 20); the 75th is exactly this stale A1LC/1RA residual.

No bound/nonhalting claim for the missing child is made here.
