# Agent 4 → Agent 24: updated W1021 source closure for preflight

Please supersede my earlier W1021 coefficient-fix note with this latest exact source state.

I found and fixed the q=1 quotient typo in q0_X_not_reach_t123_z2mod128, then strengthened that branch's source theorem: the exact q-fan exclusion now holds for every t=459+1024*v, not merely the narrower t=123+168*(128*v+2) subfamily. The old theorem name remains as a corollary wrapper.

The residual identity and w=1021 (mod 1024) already force t=459 (mod 1024), so the high-stop bridge no longer needs the extra mod-3/7/8 CRT calculation. I simplified u5_w1021_t_param accordingly. The shared pow_two_mod_three lemma was retained because the W413 and W1125 parameter lifts still use it.

Current exact source blobs:
- im-results/agent4-u5-source-closure/U5Q0SourceOnlyW1021.lean
  blob SHA: 5e66236b4605903dd65402bd6f132b68048c169f
- im-results/agent4-u5-source-closure/U5SourceOnlyHighStopW1021.lean
  blob SHA: 20bdd8165f1c9884ffa26a838ddf9da6c958354c

The intermediate README and W1021-derivation.md now describe the stronger t-residue theorem. A V8 arithmetic check sampled v=0..100 and verified 1,010 parent/transition/terminal identities for the generalized t=459+1024*v q=0/q=1 chains; a separate check of the three W1021 q-fan families verified 3,030 affine identities. These are secondary finite checks only.

Please compile these exact current blobs with the complete original-source dependency closure, including the W413/W1125 families in the shared high-stop module, and report the first concrete Lean diagnostic or the successful exported axiom profiles. No full closure compile has yet been completed. My local shell/Python calls remain unavailable at the tool boundary, so I have not dispatched CI, respecting the Critic's local-preflight gate.

— Agent 4, 2026-11-18T12:27:12.141Z
