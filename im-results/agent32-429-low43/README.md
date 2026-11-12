# Low-J deficit (4k+3): physical C/0 record entry

**Status:** the Lean module is a source-composition proof candidate pending the manual CI run. This is an intermediate result under `im-results/`, not a claim that the low-J branch is fully closed.

## Exact statement

For every (v,k\in\mathbb N), the authentic original-table run from

```lean
{state:=A, head:=0, tape:=jTape (v+2*k+2) (2*v+1)}
```

reaches the exact C/0 configuration supplied by `stage43_to_C0_delta` after

[
4v^2+18v+22
]

successful primitive moves. The endpoint has head (2v+6), state C, a blank scanned cell, and a blank right neighbour. Every earlier primitive prefix has head at most (2v+5). Thus this C/0 checkpoint is a **strict physical head record**, with its right neighbour blank.

The proof has two source-certified pieces:

1. `multi_bubble_prefix` fills the nearest (v+1) negative-even holes, taking (4(v+1)^2+2(v+1)) steps and ending at head (2v+2). `multi_bubble_prefix_head_bound` bounds every prefix of this repair by that endpoint.
2. `stage43_to_C0_delta` gives an (8v+16)-step signed source run. The physical lift splits it into a left-extremal sweep of (4v+6), a right-extremal sweep of (4v+6), and the final four-step C/0 tail. Before the final tail, the head never exceeds the stage entry head by more than 3.

The complete-tape `stage43_represented` theorem identifies the prepared zipper with `negFill (jTape (v+2*k+2) (2*v+1)) (v+1)`; no finite-window tape comparison is used.

## Authentic #429 instance

The root trajectory's J(21,11) checkpoint corresponds to (v=5,k=7), since (21=5+2\cdot7+2) and (11=2\cdot5+1). The local branch then takes (4\cdot25+18\cdot5+22=212) steps and reaches C/0 at head displacement (2\cdot5+6=16), with every earlier local head at most 15. If the preceding root prefix is established through J(21,11) at absolute head 12 with historical maximum 26, this C/0 event is at absolute head 28 and is a new global record. The root-prefix composition is a separate obligation; this file proves the uniform local branch theorem.

## Remaining gap

This result closes the physical entrance into the low-J (4k+3) C/0 corridor, not its continuation. The endpoint left context is

`1,0,1,1,1^{4v+6},(1,0)^{2k},1^6`

and the right tape is blank. The next task is to prove the exact C/0-to-E/1 / return dynamics for this context, or exhibit a genuine fatal B/001 witness. Do not infer nonhalting from the record-entry theorem alone.
