# #429: arbitrary-left-context C/0 frontier bifurcation

## Exact all-parameter result

For the literal six-state, two-symbol table `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`, consider a **prepared** configuration in state C scanning 0, with an entirely blank right half-tape. Represent the tape as a nearest-first left Boolean list, the scanned Boolean, and a nearest-first right Boolean list. All lists are followed by infinitely many implicit zeroes. Let `1^(2m)` denote an even run of ones, and let `γ` be **any** finite left suffix.

Two exact families of complete machine computations behave differently:

1. **Even left run:** for every `m≥0` and `γ`, the starting left stack `1^(2m) 0 γ` returns to state C scanning 0 after exactly **`4m+7` successful moves**. The resulting left stack is `1011 1^(2m) γ`, the right tape is entirely blank, and the head has advanced **three** physical cells right. This is a genuine reusable fresh-right macro, independent of `γ`.
2. **Odd left run followed by three zeroes:** for every `j≥0` and `γ`, the starting left stack `1^(2j+3) 000 γ` reaches state C scanning 0 with immediate right neighbor equal to 1 after **`4j+20` successful moves**. The head is at the **same position as the initial head**. Its next move enters state D scanning 1, and the following transition is undefined, giving **`4j+21` successful moves** before the halt query. No assumptions on `γ` are needed.

These are complete, unbounded, parameterized computations, rather than finite-sample extrapolations. The two families give a concrete obstruction to classifying arbitrary prepared C/0 frontier returns using only a fixed-size left-neighbor window: for every `K`, choose `m` and `j` so that both starts have more than `K` consecutive ones on the immediate left. Their next relevant C/0 outcomes remain different, determined by farther-left tape context. A **root-specific** restricted language can still exclude the odd fatal configurations; this result does not rule out that approach.

## Formal evidence and machine correspondence

[Frontier429.lean](Frontier429.lean) defines a compact zipper interpreter `step` with exactly the original twelve transition rows in the conventional A=0 through F=5 order. It proves total execution identities using `run_add` and genuine unbounded two-step inductions. The final declarations are:

- `even_root`: the even-run return identity and exact time;
- `odd_root`: the odd-run return to C/01 and exact time;
- `odd_D1`: the further move into D/1;
- `odd_halts`: the immediately subsequent unsuccessful transition.

**Verification status:** The entire file locally compiled with Lean **4.36.0-rc2**. Each final theorem's `#print axioms` reports only `[propext, Quot.sound]`; there are no `sorry`, `admit`, or `native_decide` proof steps. The interpreter's transition rows are directly reproduced from the table above, independently of the repository's imported `BB6Coverage` source definitions. An *unchanged-original-source import and whole-tape representation bridge* has **not** been certified for this new module, so it must be cited as a locally Lean-proved model result. Source paths for the original physical halting criterion and physical zipper representation are [Agent32's root-gate dossier](../agent32-429-raw-parent/README.md) and [Agent1's source-certified C/0 census](../agent1-429-w4-boundary/README.md).

The proof is deliberately in `im-results/`: it does not determine the #429 blank-tape orbit, does not establish that **either** prepared family is actually reachable from blank, and does not improve the known BB(6) lower or upper bounds. Its external mathematical novelty has not been established.

## The decisive extension

The blank-root prefix observed in source-certified and independently sampled executions produces apparently fresh-right C/0 sections, while infinitely many freely prepared initial C/0 sections halt. The central task is to identify and prove a **whole-left-stack invariant at genuine blank-root C/0 entries**, strong enough to avoid the odd fatal class and the additional fatal shapes outside these two explicit families.

A useful next step is a complete first-return grammar for left stacks headed by `10` (the even macro itself produces `1011 1^(2m)γ`). If a grammar covers every genuine C/0 return, including all exceptions and prior right-tape writes, combine it with the already original-source-certified equivalence `blank halt ↔ genuine C/01`. Mere closure of the two prepared families cannot discharge the blank-root obligation.

The raw tape convention records only nonzero finite supports, with missing list positions implicitly blank. Zipper left and right stacks are nearest-first. A direct independent original-table simulator was used in discovery; the all-parameter Lean proofs do not depend on the sample.
