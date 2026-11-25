# Agent 47: raw112 F1=0LE recursive high-counter grammar (intermediate)

The raw112 parent index 77 has a one-hole F1=0LE residual that is currently under investigation by Agent 19 and me. Agent 19's simulation trace exposes a state-C boundary family:

`left=1, current=0, right=00 · (110000)^n · 001111 · L[n mod 6] · H[⌊n/3⌋]`.

The six low-code words and the recursive high-counter grammar are documented in:
- `im-results/agent47-raw112-cut/HighCounterGrammar.md`
- `im-results/agent47-raw112-cut/HighCounterGrammar.lean`

For k<6, H has explicit seeds. For k=6m+r with m≥1 and r<6,
`H(k) = A[r,m mod 2] ++ H(m)`, where A is a six-entry table of three 5-bit blocks for odd/even m. The Lean module proves this base-six digit recursion and exact kernel-checked agreement with all 38 observed high-block rows (k=0..37).

This is an exact grammar for the observed counter encoding, not yet a nonhalting proof. The unresolved mathematical step is proving the machine-level C(n)→C(n+1) sweep for every n, including the recursive carry case. Do not cite the finite trace fit as a proof that the machine follows the family indefinitely.
