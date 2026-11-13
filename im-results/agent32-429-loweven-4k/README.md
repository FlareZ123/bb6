# #429 low-even (r=4k): parameter-uniform prepared return

**Status: Lean proof candidate; focused original-source CI pending.** This is the parameterized extension of the concrete r=32 branch in `agent32-429-loweven-r32/`. It is still a prepared-Junc return, not a blank-root nonhalting proof.

## Main theorem

`LowEven4kDelta.lean` proves the following source-level family for every (N\ge0) and (k\ge1):

[
J(N+2k,0,2N)
\longrightarrow
J(11,0,4N+4k-2)
]

in

[
\operatorname{juncPosFullTime}(N,0)+16N+18k+261
]

primitive steps, with head displacement

[
9-2(N+2k).
]

The proof includes a physical lifting theorem for every complete tape represented by the input Junc zipper. The suffix theorem is stronger than the root-relevant case: it holds for every (v\ge0), not merely even (v).

Writing (u=N+2k), the input has deficit (2u-2N=4k). The positive-u Junc sweep has time (4N^2+6N); adding the suffix gives

[
4N^2+22N+18k+261
=
4u^2+(22-16k)u+16k^2-26k+261.
]

The Lean statement deliberately retains `juncPosFullTime` rather than depending on a separate polynomial-normalization tactic.

## Suffix decomposition

For arbitrary (k\ge1,v\ge0), the new theorem proves

[
J(2k,v,0)\longrightarrow J(11,0,2v+4k-2)
]

in (8v+18k+261) steps, with displacement (9-4k). The source proof factors through:

1. the existing `juncPos_w0_exit_delta` macro and a four-step A/0-to-C/0 tail;
2. a three-step C/0-to-A/1 prefix, `af_pairs_delta`, and a four-step A/1-to-E/1 tail;
3. the existing E/1 revisit theorem;
4. a four-step C/1-to-A/0 prefix, `ar_pairs_delta`, and a four-step A/0-to-C/0 tail;
5. a six-step second C/0-to-E/1 prefix, a tail-preserving E/1 sweep, and the existing 175-step even finish-C continuation.

The proof explicitly preserves the alternating left tail and derives the source-suffix identity needed by the final continuation. No simulation table or finite tape window is used in the Lean theorem.

## Relationship to the concrete r=32 result

The concrete instance is (N=29,k=8), hence (u=45), (v=58). Its total time is

[
\operatorname{juncPosFullTime}(29,0)+16\cdot29+18\cdot8+261
=3538+869=4407,
]

and its endpoint is (J(11,0,146)) with displacement (-81). The separate r=32 dossier adds a stronger finite-prefix C/01 no-fatal guard and an exact final-suffix C/0 event census.

## Limits and next work

- The general theorem has not yet received focused CI validation.
- The parameterized theorem proves a successful original-source return and physical endpoint; it does not yet package a parameter-uniform no-fatal-prefix monitor or head-maximum bound.
- Agent 1 is handling the independent root-side prefix into (J(45,0,58)). Root composition remains necessary before claiming any blank-tape consequence.
- No all-time nonhalting result, BB(6) value, or universal upper bound follows from this prepared-return family alone.

Keep this work in `im-results/` until the parameterized proof and its root connection have been independently validated.
