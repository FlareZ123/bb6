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

An E3 seed in D is F scanning 0, blank to the left, with right tape
`11110Y`: four ones, a zero delimiter, and a finite suffix Y. Its mirror is
85 A scanning 0, with left tape `Yᴿ 0 1111` and blank right tape.

The first two 85 steps are fixed:
`A0 → B0 → C0`.
At the resulting C/0 head, the right tape is still blank. The finite left
tape, written from far left toward the head, is
`Yᴿ 0 11111 0` (the five consecutive ones include the bit written by the
first A-step). Thus, whenever this word is in the `encLeft` run-length
language, the resulting configuration is exactly a `CR_n_n` stack
configuration with the other stack L empty.

The `encLeft` definition in the DeepMind proof encodes a list of tokens
`(d,b)` as a run of (d+1) ones followed by (1+b\bmod1=1) zeroes;
the second coordinate is therefore immaterial. The relevant finite words
are concatenations of nonempty one-runs separated by single zeros, up to
irrelevant blank padding. A sufficient condition for the displayed mirrored
word to have this form is that Y has no adjacent zeros and, if nonempty,
begins with 1. This is a restricted suffix language, not arbitrary finite Y.
(The census over arbitrary Y is strictly broader.)

## 2. First-event equivalence

In D, the E3 first-event alternatives are:
- F/1, which is the actual halt; or
- F/0 with no 1 anywhere to the left of the head, which is the physical F/0 return.

Under the mirror, these are respectively:
- 85 A/1 halt; or
- 85 A/0 with no 1 anywhere to the right of the head.

After the same fixed two-step prefix A0→B0→C0, the latter is a `CR_n_n`
configuration with L empty. Therefore, on the encodable suffix sublanguage,
the desired E3 first-event theorem reduces to:

> From every stack configuration `CR_n_n L=[] R` arising from
> `Yᴿ 0 11111 0`, the 85 machine reaches either a halt or another
> `CR_n_n L=[] R'` configuration in finite time.

This is a *first-return* property, not merely closure of the stack system.

## 3. What the existing stack theorem does and does not give

The DeepMind source defines
`cfg_CR_n_n L R = encLeft R <{{C}}> encRight L`.
Its `mode_CR_n_n_closed` theorem, in the L=[] case, takes a finite run to an
EL configuration with L=[(0,0)] and R=`bumpPairHead R`.

The EL proof uses the `tok_EL` procedure and a well-founded `BoundedLex`
argument to establish finite progress to *some* stack-system mode. The
global `stack_system_closed` theorem then establishes a finite transition
to another member of CR/EL/DL/DR, or a halt.

Neither statement proves eventual return to CR with L empty. In particular,
the closure theorem cannot be silently strengthened to the first-return
property above. The remaining mathematical task is a well-founded rank (or
a stronger invariant for this initial subfamily) spanning the CR/EL/DL/DR
mode transitions and forcing either a halt or a CR/L=[] return.

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
