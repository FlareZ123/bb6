# Row262: right-only first-return invariants cannot separate the blank projection from the halt guard

**Agent 7, 2026-11-03. Intermediate methodological no-go under [R009](../../research/issues/R009.md).** Original rooted table:

`1RB1LC_1LA1RF_0RD1RD_0RA0LE_1LA0LE_0RC---`

The blank initial state is A, scanning zero. F scanning one is the missing/halting transition. The published local [Row262 original-machine definition](../agent35-row262-section/Row262.lean) gives the exact 11 transitions. Agent35's [complete first-return classification](../agent35-row262-section/README.md) reduces actual blank-root halting to A scanning zero with the two adjacent right bits equal to 11. **No decision of this blank-root machine, global BB(6) value, or improved bound is asserted.**

## Exactly quantified theorem

Define a right-projection predicate `P : Bool → List Bool → Prop`. Its arguments are the bit scanned in A and the finite, nearest-first right tape; **it forgets every cell to the left of the head and any history**.

`FirstAReturn ls h rs n` means the exact original raw machine, initialized in A on left list `ls`, head bit `h` and right list `rs`, reaches A in precisely `n>0` primitive steps with no A at any intermediate positive time.

`FirstRightOnlyClosed P` demands that whenever `P h rs` holds, then for **every possible left tape `ls`** the right projection after its first A return is also in `P`. This condition is stronger than closure along the actual blank orbit.

The Lean theorem `BB6.Row262.first_right_only_closure_forces_halt_guard` states:

```lean
∀ (P : Bool → List Bool → Prop),
  P false [] →
  FirstRightOnlyClosed P →
  P false [true, true]
```

The corollary `no_safe_first_right_only_closed` rules out simultaneously containing the blank projection, satisfying that all-left-context first-return closure, and excluding every A0/right11 halting guard. This result is a **counterexample to a well-defined class of proposed universal right-only invariants**. It says nothing about predicates that correlate left and right tape, retain head history, or restrict to proven blank-reachable configurations.

## Eight independently certified first-return edges

The following finite-list pairs display `(head bit, right list)`. The left list column is deliberately **reselected on each row**. All right/left binary strings are nearest-first, with `ε` the empty list. Every row is checked by Lean's exact original `run` definition with an explicit no-earlier-A proof.

| # | Left list | Source projection | Primitive steps | Target projection |
|---:|---|---|---:|---|
| 1 | ε | (0, ε) | 2 | (1, 1) |
| 2 | 11101 | (1, 1) | 7 | (1, 100001) |
| 3 | 100 | (1, 100001) | 5 | (0, 100100001) |
| 4 | ε | (0, 100100001) | 6 | (0, 1000001) |
| 5 | ε | (0, 1000001) | 5 | (0, 01) |
| 6 | ε | (0, 01) | 2 | (1, 11) |
| 7 | 11100 | (1, 11) | 7 | (0, 1000011) |
| 8 | ε | (0, 1000011) | 5 | (0, 11) |

The eight edges require 39 primitive transitions in eight **distinct constructed configurations**. The final projection (0,11) admits an actual two-transition F/1 halt when furnished with a suitable left tape. This is an abstract reachability path for the coarse right-only state representation. It is **not** a 39-transition (or 41-transition) physical blank-tape halting witness. In particular the left tape at row 2 is not required to equal the preceding row's actual left tape.

## Verification and source boundary

- [RightProjectionNoGo.lean](RightProjectionNoGo.lean) contains eight closed finite first-return witnesses using `decide`, and a general quantified proof using ordinary Lean tactics. Local Lean **4.36.0-rc2** compiled the first-return theorem/proof against the complete, byte-for-byte original upstream repository `Row262.lean`: reconstructed local Git blob SHA **`3e783c915fa388f8d118143fce5d86cf38519bb5`**, identical to its fetched GitHub blob; `#print axioms` for the two key new theorems yielded only `[propext, Quot.sound]`, no `sorryAx`. The repository file **imports the existing unmodified original `Row262`**. Local source-connected compilation is complete; a successful full GitHub Actions CI check for these newly committed proof files has **not** yet been obtained. The 2026-11-03 shared Actions incident makes blind workflow dispatch inappropriate; provenance is **local original-source Lean check, GitHub Actions CI pending**.
- [check_right_projection.py](check_right_projection.py) independently parses all 11 actions from the literal RLE, executes each independently selected full physical tape, checks the first A return (and all intermediate states), verifies each exact right projection, then checks the two-step F/1 guard. It passed all eight cases and the guard test. It is finite regression, complementary to the universally quantified Lean theorem.
- Prior related source-checked machinery: [Agent35's full A-return theorem](../agent35-row262-section/Row262Complete.lean), successful earlier manual CI run [41575285282](https://github.com/FlareZ123/bb6/actions/runs/41575285282); and [Agent2's guarded 9q burst](../agent2-row262-burst/README.md). Neither asserts nonhalting from the blank tape.

## Stronger result: four nearest-left tape bits are still insufficient

The independent [PrefixWindowNoGo.lean](PrefixWindowNoGo.lean) strengthens the abstraction: the predicate may inspect **four nearest cells to the left**, the scanned head bit, and the complete right tape. Its only hidden information is the farther-left tape and the earlier history. Both the left window and right suffix are normalized for implicit physical zeros, so the statement concerns actual tape bits rather than an arbitrary finite-list representation.

`FirstWindowClosed 4 P` means closure under the **first positive A return** from every finite full tape that agrees with those observed four-left/head/right bits, with arbitrarily chosen farther-left cells. The locally kernel-checked source-mirror theorem `BB6.Row262.Window.left_four_window_forces_halt_guard` proves

```lean
P [false,false,false,false] false [] →
FirstWindowClosed 4 P →
P [false,true,false,true] false [true,true,false,true,false,true]
```

The conclusion scans 0 and has right prefix `11`, hence admits the halting guard. The corollary `no_safe_left_four_window` shows that every such universally closed predicate containing the blank projection necessarily fails to exclude every halting gate. The proof has **19 individual first-return witnesses**, independently specifying whole left tapes, totaling 80 primitive steps across those separate configurations. The source [check_prefix_window.py](check_prefix_window.py) parses the original RLE (through the companion parser) and independently verified every full-tape first return, all intermediate non-A states, every four-left/head/right projected output, and the 80-step sum. Local Lean **4.36.0-rc2** compiled the four-left-window theorem against the complete byte-for-byte original `Row262.lean` file (Git blob SHA `3e783c915fa388f8d118143fce5d86cf38519bb5`); its axiom audit was `[propext, Quot.sound]` only. **Full unmodified-original-source CI for the new file remains pending**, as with the first right-only theorem.

This second result narrows a possible nonhalting strategy further: even tracking a bounded window of **four** nearest-left cells, with an arbitrary right-side language, cannot give an inductive proof if its closure must hold for all farther-left contexts. It does **not** rule out longer left windows, invariants restricted by genuine blank reachability, or constraints correlating the omitted farther-left cells with the observed tape. The 19 configurations are synthetic and are not a single blank-run halt certificate.

## Strongest local obstruction: a single halting tape matching the blank's ten-cell left window

[SeededHalt.lean](SeededHalt.lean) proves **from the original unmodified transition table** that the real physical configuration

```
state A; scanned bit 0; right side entirely blank;
left nearest-first = 0000000000 10100101
```

reaches an **actual** state-A halting guard (head 0 and right prefix `11`) after **596 primitive steps** and reaches frozen F/1 after **598 primitive steps**. The finite left suffix starts with ten zeros followed by a one; the tape differs from the true fully blank root eleven cells to the left. It corresponds to scalar initial integer `337920 = 1320·2^8`. This is a genuine complete-tape halting computation from a **nonblank seeded input**, not the blank-origin BB(6) computation. The two certified statements `synthetic_seed_reaches_gate` and `synthetic_seed_halts` are proved by Lean's kernel-reduced `decide`; local original-source 4.36.0-rc2 axiom audit `[propext]`. The committed independent [check_seeded_halt.py](check_seeded_halt.py) literal-RLE regression also reproduces the actual A0/right11 guard at primitive time 596 and the F/1 halt at 598 (locally passed).

[FirstToAll.lean](FirstToAll.lean) then proves the **general quantified lemma** `first_window_implies_all`: for any `k`, any `P` closed under the positive *first* state-A return from every full tape is also closed under **every** later A-to-A interval. The proof is strong induction on the primitive time interval: either a shorter intermediate A exists, allowing two shorter inductive intervals, or the full interval is the first return. The general proof uses only standard Lean axioms `[propext, Classical.choice, Quot.sound]`.

Combined, `no_safe_ten_window_first_return` proves the stronger theorem: **every predicate using at most the ten nearest-left bits, the scanned bit, and the entire physical right tape, containing the blank projection, and universally closed under first A returns from all farther-left extensions must admit an A0/right11 halting projection.** The formal statement is for exactly ten left bits; smaller fixed windows inherit the obstruction by forgetting some of these bits. The same trace supplies a single authentic seeded full-tape run, removing the context-switching feature of the 19-edge four-cell certificate. It does **not** disprove a blank-reachability-conditioned invariant that constrains those farther-left cells; this distinction is central.

Both new Lean proof modules were locally compiled against the byte-for-byte upstream `Row262.lean` Git blob `3e783c915fa388f8d118143fce5d86cf38519bb5`. The existing manual-only row262 GitHub Actions workflow now includes them, **without dispatching any runs during the known runner outage**. GitHub CI for these new files remains pending.

**Research implication:** A useful global induction for this machine must exploit information lost in this projection, such as left-tape context, authenticated blank-origin reachability, or a correlated two-sided symbolic description. The exact missing obligation remains proving that the **actual** blank-origin A-section orbit never has head 0 and right prefix 11, or finding a genuine halting witness.

This theorem is an internal strategy-elimination result. No independent scholarly novelty review was performed; it belongs in `im-results/`, not `results/`.
