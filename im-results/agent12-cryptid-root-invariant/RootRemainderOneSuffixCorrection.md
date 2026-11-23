# Corrected suffix in the remainder-one reset

**Status:** source-branch derivation and Lean proof draft added; the new theorems in
`RootRemainderTwoToken.append.lean` have not yet passed the original-source CI
build. Treat the formulas below as a checked-by-hand endpoint correction, not
as a kernel-certified root theorem.

## Corrected map

The source stack clauses give
[
D_n(1;[5]) longrightarrow^+ D_0(8n+11;[0,0,0,2]),
]
not `D_0(8n+11;[0,0,2])`.

The discrepancy is the DR positive-positive branch. Immediately before it,
the configuration is
[
DR(0,1,0^{4n+6},1; [1,0,2]).
]
Applying the source `root_countdown_dr_positive_positive_step` with
`a=b=0` consumes the leading 1s and prefixes three zeros to the remaining
right suffix `[0,2]`. Thus its exact endpoint is
[
CR(0^{4n+7}1; [0,0,0,0,2]),
]
with **four** zeros before 2. The subsequent CR-zero sweep increments the
first zero counter and leaves `[0,0,0,2]` behind; CR-one/empty produces
[
EL([0]; [0,8n+17,0,0,0,2]).
]
The suffix-preserving 16-step general-tail macro then gives the stated
`D_0(8n+11;[0,0,0,2])`.

The outer-successor and raw-step counts in the existing dossier are unchanged;
only the untouched suffix at the endpoint changes.

## Lean proof draft

The following declarations have been added to
`RootRemainderTwoToken.append.lean`:

- `root_countdown_cr_one_zero_step`: the exact five-step CR `[1,0]` branch;
- `root_countdown_cr_zero_sweep_pair`: a CR-zero sweep preserving an
  arbitrary right suffix;
- `root_countdown_general_tail_with_suffix`: the 16-step tail generalized
  to arbitrary untouched suffixes;
- `root_countdown_one_reset`: (D_n(1)	o D_0(8n+7;[5]));
- `root_countdown_one_five_reset`: the corrected
  (D_n(1;[5])	o D_0(8n+11;[0,0,0,2])).

These are proof drafts until the pinned source module compiles them and the
public theorem axiom audit is clean.

## Consequence for the blank-root path

The arithmetic continuation in `RootRemainderOneTail.md` should therefore
be revisited at its final suffix: the candidate endpoint is
`D_0(26,524,315;[0,0,0,2])`, not
`D_0(26,524,315;[0,0,2])`.

The next token-normalizer input already recorded in that dossier,
`tok_DR([2,0],[],0^3 1 0^(4n+6)1)`, is in fact consistent with the corrected
suffix. Starting from `D_n(1;[0,0,0,2])`, the DL-zero branch consumes the
first zero and two subsequent EL-zero branches consume the remaining two;
the resulting DL left stack is `0^3 1 0^(4n+6)1`. Thus the suffix correction
does not by itself invalidate the token-normalizer route. That exact alignment
still needs to be included in the kernel proof. In particular, this correction
does **not** yet establish blank-root nonhalting.
