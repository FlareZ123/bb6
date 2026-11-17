# Blank-root A-state prefix automaton: suffix parsing and a finite audit

**Status:** intermediate research, not a proof of nonhalting. This is a candidate direct-tape route for the #623 holdout, developed from the A-state macro analysis in [Agent 24's note](../agent24-machine623-macro-invariant.md). It does not change the BB(6) status.

## 1. A-state representation

At an A-state with head position h, let l be the leftmost position visited so far and let

```
P = tape[l], tape[l+1], …, tape[h-1]
d = h-l
b = tape[h]
r1,r2,r3 = tape[h+1], tape[h+2], tape[h+3].
```

The observed prefix property is

- if P is nonempty, its first bit is 1;
- P has no adjacent `00`.

Call this `PrefixOK(P)`. The boundary observations additionally include:

- d=0: b=0 and the right triple is not `100`;
- d=1 and b=0: the right triple is not `000`;
- d=1 and b=1: the one-cell prefix is 1.

The exceptional d=3/A1 state needs more than PrefixOK: its prefix is `101`, and r1=1.

## 2. The A/1 branch is a suffix parser

Write P as `p₀…p_{d-1}`, with p₀=1 when d>0. On A/1, the machine writes 0 at h, then E writes 1 at p_{d-1}. The next branch is determined by the second-last prefix bit:

| suffix `(p[d-2],p[d-1])` | macro path | prefix change | new A head bit |
|---|---|---|---|
| `00` | E/0 → F/0 | halt | — |
| `01` | E/1 → C/0 → D/1 | pop 2 symbols | 0 |
| `10` | E/0 → F/1 | pop 3 symbols | `p[d-3]` |
| `11` | E/1 → C/1 | pop 3 symbols | `p[d-3]` |

Under PrefixOK, the `00` case is excluded. Thus A/1 repeatedly pops 3 symbols whenever the second-last symbol is 1; it stops with a zero head when the second-last symbol is 0 and the last is 1.

Define the regular language

```
Danger(P)  iff  P ∈ (11[01])⁺.
```

Equivalently, d is a positive multiple of 3 and every aligned 3-symbol block of P begins with `11`. A four-state DFA recognizes it:

- q0: block boundary;
- q1: first bit of a block was 1;
- q2: first two bits were 11;
- qdead: a required 1 was missed.

Transitions are q0 --1→ q1, q0 --0→ qdead; q1 --1→ q2, q1 --0→ qdead; q2 --0/1→ q0; qdead loops. Accept q0 only after a nonempty input.

**Exact macro interpretation:** given PrefixOK, Danger(P) is precisely the obstruction to an A/1-only suffix-parsing chain reaching the visited left frontier with head bit 1. If a parsed triple does not begin `11`, the parser stops before the frontier with head bit 0; if the length is not divisible by 3, the final move lands in blank space. The d=3 boundary is the first instance: a length-three prefix beginning `11` is dangerous, while `101` takes the safe pop-2 path.

This is a statement about the A/1 macro, not yet a full-machine invariant.

## 3. Exact A/0 preimages of Danger

For A/0, the machine writes 1 at h; B preserves r1; C inspects r2.

1. **C/1 (`r2=1`):** return A at h+1. The new prefix is `P ++ [1]`, and the new head bit is r1. A dangerous A/1 state is created exactly when r1=1 and `Danger(P ++ [1])`.

2. **C/0, D stops at h+1 (`r2=0,r3=0,r1=1`):** return A at h with prefix P unchanged and current bit 1. A dangerous A/1 state is created exactly when `Danger(P)`.

3. **C/0, D reaches the A-written 1 (`r1=r2=r3=0`):** return A at h-1. The new prefix is `P.dropLast`, and the new head bit is the old last bit of P. A dangerous A/1 state is created exactly when the old last bit is 1 and `Danger(P.dropLast)`.

All other A/0 return cases have new head bit 0.

This gives a finite list of preimage conditions that an inductive invariant must exclude. A candidate strengthening is:

```
PrefixOK(P)
∧ (b=1 → ¬Danger(P))
∧ (d=3 ∧ b=1 → r1=1)
∧ (b=0 ∧ r1=r2=1 → ¬Danger(P ++ [1]))
∧ (b=0 ∧ r1=1 ∧ r2=0 ∧ r3=0 → ¬Danger(P))
∧ (b=0 ∧ r1=r2=r3=0 ∧ last(P)=1 → ¬Danger(P.dropLast))
∧ the d=0 and d=1 boundary clauses above.
```

The list append/drop operations make these predicates amenable to Lean proofs by case analysis and regular-language lemmas. **The displayed conjunction is a candidate, not a proved inductive invariant:** closure of every clause under every A→A macro case remains to be established.

## 4. First closure obstruction

The displayed conjunction is **not inductive**. Here is a concrete synthetic A-state satisfying every displayed clause:

- (d=6), (P=110101), current bit (b=1), and (r_1r_2r_3=000).
- (P) starts with 1 and has no adjacent 00.
- (P\notin D), since its aligned blocks are 110 and 101.
- None of the (d=0,1,3) boundary clauses or the A/0 preimage clauses applies.

The A/1 macro has suffix 01. It pops two symbols and returns to A with (d=4), (P'=1101), current bit 0, and right triple 000. This successor violates the displayed A/0 drop-last clause: its last prefix bit is 1 and (P'.dropLast=110\in D).

The next A/0 macro (the D sweep across the three right-hand zeros) returns to A with (d=3), prefix 110, and current bit 1. The A/1 macro then returns to the left frontier with current bit 1; the following A/1 macro reaches F/0 and halts. This is a counterexample to *inductiveness of the predicate*, not a claim that this synthetic configuration is reachable from the blank root.

The first missing A/1-preimage obligations for the three A/0 clauses are exact. Write (D=(11[01])^+\).

1. **A/1 pop-2:** if (P=Q\,01), the successor has prefix (Q), current bit 0, and right triple (00r_1). It violates the A/0 drop-last clause exactly when (Q=R\,1), (R\in D), and (r_1=0). Thus an invariant must imply
   [
   b=1\ \land\ P\in D\,101\quad\Longrightarrow\quad r_1=1.
   ]
2. **A/1 pop-3 through suffix 11:** if (P=Q\,011), the successor has right triple 110. It violates the A/0 append clause when (Q\,1\in D), equivalently (P\in D\,11011). This pattern must be excluded at A/1.
3. **A/1 pop-3 through suffix 10:** if (P=Q\,010), the successor has right triple 100. It violates the A/0 same-prefix clause when (Q\in D), equivalently (P\in D\,010). This pattern must be excluded at A/1.

These are necessary first closure conditions, not a completed strengthening. Their own A/0 preimages still need closure analysis; simply appending them to the candidate would not yet be a proof.

## 5. Reproducible finite audit

The accompanying [`blank_root_prefix_audit.cpp`](blank_root_prefix_audit.cpp) implements the raw six-state transition table, tracks the visited prefix and the Danger DFA state, and checks the candidate obstructions. Run:

```bash
g++ -O3 -std=c++17 blank_root_prefix_audit.cpp -o prefix_audit
./prefix_audit 50000000
```

A local 50,000,000-primitive-step run produced:

| Check | Count |
|---|---:|
| A-state visits | 14,994,938 |
| A/1 visits | 4,998,204 |
| A/0 visits | 9,996,734 |
| prefix contains adjacent `00` | 0 |
| nonempty prefix does not start with 1 | 0 |
| d=0 with current bit 1 | 0 |
| d=0 with right triple `100` | 0 |
| d=1, A/0 with right triple `000` | 0 |
| A/1 with `Danger(P)` | 0 |
| d=3, A/1 | 1 |
| d=3, A/1 with r1=0 | 0 |
| d=3, A/1 with prefix other than `101` | 0 |
| A/0 C/1 preimage `Danger(P ++ [1])` | 0 |
| A/0 D-stop-at-h preimage `Danger(P)` | 0 |
| A/0 D-stop-at-h−1 preimage `Danger(P.dropLast)` | 0 |

The run did not halt within the 50M-step horizon. The unique d=3/A1 state had prefix `101` and r1=1; its A/1 macro returned at d=1 with current bit 0 and right triple `001`. The reported 50M counters predate the A/1 closure-obstruction analysis above; they do not count the three newly identified A/1 preimage patterns.

These are finite computational observations only. They do not imply an all-time bound or nonhalting.

## 6. Proof work still required

1. Define the A-state macro over a list prefix and a right-hand tape window, and prove its equivalence to the raw machine transitions.
2. Formalize PrefixOK and the Danger DFA; prove the append, pop-2, pop-3, and drop-last lemmas.
3. Prove closure of the full candidate invariant under every A→A case. If closure exposes further conditions, compute the finite product automaton rather than enlarging a raw fixed tape window.
4. Connect the invariant to the original blank-start configuration and derive exclusion of the F/0 halting transition.

No claim about the fate of machine #623 or the exact value of BB(6) follows until these universal steps are proved.
