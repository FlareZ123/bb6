# E3 finite-suffix first return: mirror reduction and blocked stack bridge

**Status:** exact mirror reduction and a three-step entry into the DeepMind DL stack mode for a restricted suffix language. The first-return theorem remains open. This note does not claim E3 totality, a blank-root result, or a BB(6) result.

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
with tape reflection `i ↦ -i`. Each of the twelve nonhalting transitions
is preserved by this mirror, and D_F1 halt maps to 85_A1 halt.

An E3 seed in D is F scanning 0, blank to the left, with four 1s at
positions 1 through 4, a zero at position 5, and a finite suffix Y beginning
at position 6. Under the mirror, this is 85 A scanning 0, with 1s at positions
-1 through -4, a zero at -5, the reversed suffix on positions -6 and farther
left, and a blank right tape.

The first three 85 steps are fixed:
`A0 → B0 → C0 → D0`.
At the resulting D/0 head, the left tape from nearest to farthest is
`1 0 11111 0 Y`: the first 1 is written by A0, the next 0 by B0, the
five consecutive 1s consist of the four original 1s plus the 1 written by
C0, and the delimiter 0 precedes Y. The right tape begins with the current
blank 0 and is blank thereafter.

This is exactly a `DL_0_n` stack configuration
`cfg_DL_0_n L=[] R` whenever the finite word
`1 0 11111 0 Y` is in the `encLeft` run-length language. A sufficient
condition is that Y is empty, or begins with 1 and has no adjacent zeros:
then the displayed left word is a concatenation of nonempty 1-runs
separated by single zeros, with the final blank providing any trailing
separator. The run lengths determine R (with second coordinate 0). This is
a genuine three-step stack-entry lemma for that suffix language, unlike the
naive two-step CR entry, which fails because its head-adjacent left cell is 0.

The first-event correspondence is exact: D F/1 maps to 85 A/1 halt, and D
F/0 with no 1 anywhere to the left maps to 85 A/0 with no 1 anywhere to the
right. After three further steps from that A/0 boundary, 85 again reaches a
`DL_0_n` configuration with L empty, provided the returned suffix is in the
same run-length language. Thus, on this language, the E3 first-event problem
is equivalent to a first-return problem for the 85 stack system: from
`DL_0_n L=[] R`, eventually reach another `DL_0_n L=[] R'` (the E3
return), or halt.

## 4. Relation to existing E3 evidence

The repository's E3 finite census checks 67,108,862 suffixes through length
26 and reports an event in every case, with maximum observed time 398.
The remote-reentry DAG is a conservative finite abstraction; its cycles
show why arbitrary remote reentry alone does not prove finite-tail totality.
Both are computational evidence, not a proof for all finite Y.

The three-step DL entry is valid for the stated run-length suffix language.
It does not yet establish that every root-reachable E3 suffix belongs to
that language; this must be proved from the upstream source grammar. It also
does not prove that the DL/EL/DR/CR stack-mode trajectory returns to DL with
L empty. The DeepMind `stack_system_closed` theorem gives a finite
transition to *some* stack mode or halt, which is weaker than the needed
first-return property.

## 5. Correct next proof target

There are two precise remaining obligations.

1. Prove that every E3 suffix Y actually reachable from the blank-root
   trajectory is empty or begins with 1 and contains no adjacent zeros.
   Then the three-step entry above applies uniformly to root-reachable
   E3 seeds.

2. Strengthen the stack-mode analysis to prove, for the corresponding
   `DL_0_n L=[] R` inputs, eventual return to another `DL_0_n L=[] R'`
   configuration or halt. Reaching an arbitrary CR/EL/DL/DR mode is not
   sufficient.

The first obligation is a language-invariant problem; the second is a
well-founded first-return problem across the stack modes. Neither is proved
here.
