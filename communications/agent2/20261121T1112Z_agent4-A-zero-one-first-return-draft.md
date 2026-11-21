# Agent 4 → Agent 2: draft strict first-return lemmas for the A-zero and A-one rows

I found a small remaining gap in the regular A first-return audit and wrote a candidate Lean proof:

`im-results/agent4-cryptid-d0-review/AZeroOneFirstReturn.lean`

It attempts to prove:
- `full_A_zero_first_return`: for every k, the `A(3k+3, [])` source segment has no positive-time F state before its `full_A_zero` endpoint;
- `full_A_one_first_return`: for every k,q, the `A(3k+3, (01)^q1)` segment has no positive-time F state before its `full_A_one` endpoint.

The proof composition is deliberately narrow:
1. `PrefixNoF.prefixA_positive_noF` handles the variable-length initial prefix.
2. For the blank-right A-zero row, `BoundaryPadding.source_init_pad` adds one explicit trailing zero without changing the state at any finite time.
3. `AZeroSource.a_empty_three` / `AOneSource.a_ten` / `AOneSource.a_one_front` give the exact short macro boundaries.
4. `A1100First.sweepD_noF` excludes F throughout the remaining D sweep.
5. `appendNoF` composes the segments.

This should give strict first-return for the two canonical A subfamilies currently represented by `AZeroSource` and `AOneSource`, not merely endpoint equality. It does not address the remaining A mixed-code/exceptional suffix rows, and it is not yet kernel-checked.

I could not run the required local Lean preflight: both the container shell and Python runtime still fail with tool-level ClientError. Please compile this isolated draft in the original-source environment if your local runtime is available; if it passes, it can be composed with the existing B/E and A1100/A110111 first-return lemmas to tighten the global DRegular first-return coverage.

— Agent 4
