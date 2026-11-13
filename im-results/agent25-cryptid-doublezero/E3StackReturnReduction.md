# E3 finite-suffix first return as a stack-system problem

**Status:** reduction and representation bridge; the first-return theorem remains open. This note does not claim E3 totality, a blank-root result, or a BB(6) result.

## 1. Exact machine mirror

The D-start machine is

```
A0 1RB    A1 0RE
B0 1LC    B1 0RA
C0 1LA    C1 1LD
D0 1LC    D1 1LF
E0 0LC    E1 0LB
F0 1LE    F1 halt
```

The DeepMind #85 machine has table

```
A0 1RB    A1 halt
B0 0RC    B1 0RE
C0 1RD    C1 1RF
D0 1LE    D1 0LB
E0 1RC    E1 0LD
F0 1RC    F1 1RA
```

The state permutation is
`D_F→85_A, D_E→85_B, D_C→85_C, D_A→85_D, D_B→85_E, D_D→85_F`,
with tape reflection (imapsto-i). Each of the twelve nonhalting transitions
is preserved by this mirror, and D_F1 halt maps to 85_A1 halt.

An E3 seed in D is F scanning 0, blank to the left, with four 1s at
positions 1 through 4, a zero at position 5, and a finite suffix Y beginning
at position 6. Under the mirror, this is 85 A scanning 0, with 1s at positions
-1 through -4, a zero at -5, the reversed suffix on positions -6 and farther
left, and a blank right tape.

The first two 85 steps are fixed:
`A0 → B0 → C0`.
The head is then at position 2 in state C scanning 0. Its head-adjacent
left cell (position 1) is 0, written by the B0 step. By contrast,
`encLeft R` has head bit 1 whenever R is nonempty
(the source lemma `encLeft_head`). Since this configuration has a nonempty
left tape but head-adjacent bit 0, it is **not** a `CR_n_n` configuration
of the DeepMind stack system. This blocks the naive two-step bridge; no
condition on the remote suffix Y can repair this fixed local mismatch.

The first-event correspondence itself is exact: D F/1 maps to 85 A/1 halt,
and D F/0 with no 1 anywhere to the left maps to 85 A/0 with no 1 anywhere
to the right. Thus the E3 problem becomes a first-return problem for 85 from
the reflected A/0 seed to an A/0 boundary with blank right, or halt.

A useful next question is whether a *longer, explicitly source-verified
prefix* from this A/0 seed reaches one of the four encoded stack modes
CR/EL/DL/DR. If so, the suffix language must also be checked against the
exact `encLeft`/`encRight` conventions. The pair-stack reduction cannot
be applied before that entry lemma is proved.

## 4. Relation to existing E3 evidence

The repository's E3 finite census checks 67,108,862 suffixes through length
26 and reports an event in every case, with maximum observed time 398.
The remote-reentry DAG is a conservative finite abstraction; its cycles
show why arbitrary remote reentry alone does not prove finite-tail totality.
Both are computational evidence, not a proof for all finite Y.

The stack bridge potentially narrows the problem for root-reachable suffixes:
if the actual E3 suffix language is shown to lie in the `encLeft` language,
then the existing pair-stack reduction applies to every such seed. The
first-return theorem remains the missing step. Even a proof for this
restricted language would not establish totality for arbitrary finite Y
without a separate argument.

## 5. Next proof target

Prove a source-level theorem for the stack system with initial mode
`CR_n_n`, L empty, and R in the image of the run-length encoding above:

```
∃ R', Reaches (cfg_CR_n_n [] R) (cfg_CR_n_n [] R') ∨
       ∃ cfg, Reaches (cfg_CR_n_n [] R) cfg ∧ step cfg = none
```

Then transport this result through the exact mirror and the two-step prefix
to the D E3 first-event classification. If the proof only reaches an
arbitrary stack mode, it has not closed the E3 no-event branch.
