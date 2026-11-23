# Remainder-one reset: endpoint audit and open token boundary

**Status:** source-branch endpoint derivation and Lean proof draft added; the
new declarations in `RootRemainderTwoToken.append.lean` have not yet passed
the pinned original-source CI build. No new blank-root theorem is claimed.

## Exact [5] reset endpoint

The initial proposed extra-zero correction was **wrong**. The exact source
statement for `root_countdown_dr_positive_positive_step` has output right
stack `(0,0)::(b,0)::R`: two cells. For the [5] reset, after DR-zero the
right stack is `[1,0,2]). DR-positive-positive with (b=0) and
(R=[0,2]) gives `[0,0,0,2]` (three zeros before 2). The subsequent
CR-zero sweep increments the first zero counter and leaves `[0,0,2]);
CR-one/empty then gives
[
EL([0];[0,8n+17,0,0,2]).
]
The suffix-preserving general-tail map therefore yields
[
D_n(1;[5]) longrightarrow^+ D_0(8n+11;[0,0,2]).
]
The original endpoint in `RootRemainderOneTail.md` is supported. The
temporary claim of an endpoint ending in `[0,0,0,2]` has been retracted.

## Remaining token-boundary discrepancy

There is a separate, unresolved question about the next DL-right-one branch.
Starting from `D_n(1;[0,0,2])`, the stack-level sequence appears to be:

1. fixed prefix and EL-zero sweep;
2. EL-positive on 1;
3. DL-zero consumes the first zero, leaving `[0,2]`;
4. one EL-zero consumes the remaining zero;
5. EL-positive on 2;
6. DL-right-one invokes `tok_DR_2_0_closed`.

This accounting appears to pass the left stack
`[0,0,1] ++ replicate (4*n+6) 0 ++ [1]` to the token conversion, i.e.
a `0^2 1 ...` prefix. The dossier currently records `0^3 1 ...`.
A private proof draft, `root_d1_suffix_two_to_tok_DR`, has now been added
to the same append file with that exact `tok_DR([2,0],[],0^2 1 ...)`
endpoint. It remains unverified until the pinned source module compiles.

## Lean proof draft

The following declarations have been added to
`RootRemainderTwoToken.append.lean`:

- `root_countdown_cr_one_zero_step`: the exact five-step CR `[1,0]` branch;
- `root_countdown_cr_zero_sweep_pair`: a CR-zero sweep preserving an
  arbitrary right suffix;
- `root_countdown_general_tail_with_suffix`: the general-tail map for
  arbitrary untouched suffixes;
- `root_countdown_one_reset`: (D_n(1)	o D_0(8n+7;[5]));
- `root_countdown_one_five_reset`: (D_n(1;[5])	o
  D_0(8n+11;[0,0,2])).

These remain proof drafts until the pinned source module compiles them and
the public theorem axiom audit is clean. The arithmetic continuation to
`D_0(26,524,315;[0,0,2])` is not independently certified by this document.
