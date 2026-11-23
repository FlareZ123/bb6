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

## Exact token boundary after the [0,0,2] reset

The dossier's `0^3 1 0^(4n+6)1` token input is correct. My temporary
`0^2` concern omitted the zero written by EL-positive(1):

1. After the fixed prefix and EL-zero sweep, the EL right stack is
   `[1,0,0,2]`.
2. EL-positive(1) writes a zero, so the DL right stack is
   `[0,0,0,2]`.
3. DL-zero consumes the first zero, leaving `[0,0,2]`.
4. Two EL-zero transitions consume the remaining two zeros.
5. EL-positive(2) enters DL with left stack
   `[0,0,0,1] ++ replicate (4*n+6) 0 ++ [1]` and right stack `[1]`.

The private proof draft `root_d1_suffix_two_to_tok_DR` now includes both
EL-zero transitions. The explicit tape definition `root_d1_token_cfg`
encodes the three-zero prefix. The earlier 0^2 warning is retracted.

## Lean proof draft

The following declarations have been added to
`RootRemainderTwoToken.append.lean`:

- `root_countdown_cr_one_zero_step`: the exact five-step CR `[1,0]` branch;
- `root_countdown_cr_zero_sweep_pair`: a CR-zero sweep preserving an
  arbitrary right suffix;
- `root_countdown_general_tail_with_suffix`: the general-tail map for
  arbitrary untouched suffixes;
- `root_countdown_one_reset`: (D_n(1)	o D_0(8n+7;[5]));
- `root_countdown_one_five_reset`: (D_n(1;[5]) -> D_0(8n+11;[0,0,2]));
- `root_countdown_step_with_suffix` and the three residue iterators:
  suffix-preserving countdown for arbitrary untouched token tails;
- `root_d1_suffix_two_to_token_cfg`: explicit-tape endpoint for
  `tok_DR([2,0],[],0^2 1 0^(4n+6)1)`;
- `root_remainder_one_root_to_token_cfg`: countdown from
  `D_0(26,524,315;[0,0,2])` to that explicit token configuration.

These remain proof drafts until the pinned source module compiles them and
the public theorem axiom audit is clean. The preceding arithmetic path to
`D_0(26,524,315;[0,0,2])` remains conditional on its earlier reset and
offset-six compositions.
