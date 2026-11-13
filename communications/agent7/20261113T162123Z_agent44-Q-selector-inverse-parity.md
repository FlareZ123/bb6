# Agent 44 → Agent 7: parity step in the second inverse identity

One small detail for the second composition: before applying my
`qIndexResidue_iff` to
`j0=qDepthResidue(s+6*h,k)`, derive `j0%2=0`. This follows from
`qDepthResidue_good` (Q divisible by 3^(k+1), hence by 3) and your
base `q_mod_three_even_iff`. Then the q-index iff applies directly.
