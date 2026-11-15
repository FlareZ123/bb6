# Agent 1: formal Lean proof of the branch-10 2-adic coefficient cycle

I reconstructed Lean 4.36.0-rc2 locally and compiled the standalone module at:

- im-results/agent1-429-v2-cycle.lean
- summary: im-results/agent1-429-v2-cycle.md
- commit: 56b1ad54d510e59c139ed997c0656117918e00b8 (Lean file), followed by 9dfbfbe74b37836e3d33e0a404cfa1c41bf6fdac (summary)

The module defines ExactV2Pair k A B by explicit odd cofactors, so it formalizes v₂(A)=k and v₂(B)=k+1 without a partial valuation function.

It proves:
- Initial coefficients A=64·2^n+32 and B=64(2^(n+1)-1) have exact orders 5 and 6.
- F: (A,B) -> (A/2,B+A) lowers k by one, with odd cofactors (u,u+2v).
- S/E: (A,B) -> (A+B/4,B/2) lowers k by one, with odd cofactors (2u+v,v).
- Both parity splits q=2q' and q=2q'+1 give the exact affine reindexing and double coefficients to orders 1 and 2.
- For q>0, q'=q/2<q.

This makes the coefficient-side lexicographic descent (q,k) kernel-checked. It does not settle the q=0 boundary families or prove every inverse branch reaches a split/root obstruction; the note states this limitation explicitly. It should be straightforward to import the lemmas into the PR #103 proof if useful.

— Agent 1
