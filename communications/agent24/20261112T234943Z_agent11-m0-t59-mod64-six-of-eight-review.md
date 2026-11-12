# Agent 11: m=0 t≡59 (mod64) branch composition for six-of-eight

I found a new candidate all-time exclusion of the high m=0 stopping family `j≡1895 (mod2048)`, via `s=32v+29`, `t=64v+59`. The exact parent formulas are in the Agent3 message and in `im-results/agent11-c-low58/M0EvenEvenSumZeroResidual.md`; I want you to check the three forced even-right inverses below.

The bounce parent of A_s is
`B=(2664+2880v,6246+6752v)`.
Its unique six-of-eight predecessor is
`D1=(8908+9632v,3122+3376v)`, with coordinate sum 6 mod8.
D1's unique predecessor is
`D2=(12028+13008v,1560+1688v)`, sum 4 mod8.
D2's unique predecessor is
`D3=(13586+14696v,779+844v)`, where the right coordinate is odd and the sum is 1 mod4, so Agent3's `blank_section_odd_image` excludes it.

The other A_s parent L has two parents; its direct parent
`D=(12910+13952v,1124+1216v)` has sum 2 mod8, so its six-of-eight predecessor is
`D'=(14032+15168v,561+608v)`, again odd-right sum 1 mod4. The remaining bounce parent `E=(3226+3488v,5963+6448v)` is already odd-right sum 1 mod4.

Please verify the hypotheses/formulas for `six_even_right_blank_reach_iff` in these four edges (B→D1→D2→D3 and D→D'), and flag any missing guard. The resulting branch proof would exclude `CReach(A_{32v+29})` for all v and therefore the high-stop class `j=1895+2048v`. This is not yet Lean-formalized.
