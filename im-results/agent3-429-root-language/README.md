# #429 blank-root C/0 section language and an all-parameter fatal member

**Scope, 9 November 2026:** Exact six-state, two-symbol machine `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`. This dossier combines a quantified, Lean-proven **synthetic prepared-tape fatal family** with an explicitly finite **genuine blank-origin grammar candidate**. It does not settle the authentic blank run, machine #429, or BB(6). It belongs in `im-results/` until there is a decisive root-connected theorem.

## Proved, for all parameters

Take an arbitrary natural number `m`. Begin in state C scanning 0, with blank right half-tape and nearest-first left word

    101110 1^(2m)

followed by blanks. The explicit finite zipper left list in the proof includes one terminal 0 representing the first blank. The exact all-parameter zipper identity is

    run (46+8*m) (C, 101110 1^(2m) 0, 0, [])
      = some (C, (10)^(m+2) 1^6, 0, [1]).

The machine therefore reaches a fatal C/0 scanning zero with its immediately-right cell marked 1. A C/0 instruction enters D/1, whose transition is undefined, giving `run (48+8*m) = none`. The formulas hold **for all m**, through genuine primitive steps; they are not a fit to a finite sample.

- [BB429RootLanguageFatal.lean](BB429RootLanguageFatal.lean) proves both parameterized identities by explicit source transition macros and induction. It imports the exact literal-table [Frontier429](../agent39-429-frontier-left/Frontier429.lean) model and uses existing proven AE/AB/CP sweeps. Lean 4.36.0-rc2 verified both theorems with axioms **only** `[propext, Quot.sound]`; original unchanged-model CI [42630484807](https://github.com/FlareZ123/bb6/actions/runs/42630484807) succeeded.
- [BB429RootLanguageCast.lean](BB429RootLanguageCast.lean) proves a **generic one-step and all-time bisimulation** from the literal-table model into the repository's independently existing original `BB429OddExcursion` zipper. The translated family identity therefore holds for the original zipper interpreter, with no new interpreter assumptions. The local Lean kernel checked it; `one_cast` has no axioms, `run_cast` has only `[propext]`, and the family theorem has only `[propext, Quot.sound]`.
- [BB429RootLanguagePhysical.lean](BB429RootLanguagePhysical.lean) lifts the quantified family into the unmodified original `BB429PhysicalFrontier.target429` **bi-infinite physical tape**, using the existing exact simulation theorem `BB429PhysicalBridge.source_run_rep`. It proves physical fatal-gate existence and the next-two-query halt, **conditional on the explicitly displayed prepared whole-tape representation**. It makes no assertion that the prepared input is reachable from blank. The pinned original-source CI [42631709015](https://github.com/FlareZ123/bb6/actions/runs/42631709015) **passed**, compiling all imported authentic source semantics and checking that both physical theorems exclude `sorryAx`, with axioms only `[propext, Quot.sound]`.

The `m=3` input is `101110111111`: one leading singleton 1, a length-3 internal 1-run, and a terminal length-6 run. This word is in the observed compact blank-root C/0 **syntax** below, although the actual blank run has not been shown to reach this particular word. Thus even the stronger candidate syntax fails as a standalone safety condition on *arbitrary* prepared tapes.

## Root-origin grammar candidate, finite evidence only

At each **genuine blank-origin** C/0 instruction start, build the left word by reading the physical tape from immediately left of the head down to its leftmost marked 1, with all intervening zeros included. Only the nonterminal states of the real machine are simulated.

A direct exact C++17 source-table probe, [root_grammar.cpp](root_grammar.cpp), records the following two *candidate* word types:

    I(a,m)   = (10)^a 1^(2m)                    (even terminal 1-run)
    II(a,k,b)= (10)^a 1^(2k+3) 0 (10)^b 1^6    (one odd long run)

In observed type II words, `a` was either 0 or 1, all remaining nonterminal marked runs were isolated 1s, and every zero separator was isolated. The type I filter allows arbitrary `a` (the probe does not claim that every such word is reached). These syntax classes refer to **nearest-first left words** and require the right half-tape blank at a right-head-record C/0.

The true-blank primitive simulator ran exactly **1,000,000,000 defined transitions** (without a halt); at the **437 C/0 events**, it classified **104 as type I** and **333 as type II**, with **zero outside the proposed grammar**. Every observed C/0 was a strict new global head-right record and had a blank immediately-right cell. The scanned head range was from **−5,468 through +1,466**. Compile the standalone code with a conforming C++17 compiler and run it to reproduce those observations. The bounds in its fixed tape buffer exceed the observed range. These are **finite observations, not an induction or nonhalting proof**. Agent36 previously recorded 222 strict record C/0 events within 100 million steps; this extends the classification to one billion.

**Crucial distinction:** the all-parameter fatal family and the finite blank-run grammar evidence are compatible. Type II includes a parameter choice `a=1,k=0,b=0` that halts when prepared artificially. To prove actual nonhalting, a root-connected invariant must constrain the *numerical parameters and temporal ancestry* of genuine C/0 records. The raw language alone is insufficient.

## Root-connected next research target

Prove a complete symbolic first-return map on the type-I/type-II parameter families and an **inductively closed restriction** covering the genuine blank origin `C/0` with nearest-first left word `11`. The difficult cases are type I with a single leading `10` and type II with `a=1`; they can express fatal prepared inputs. Source-level preparatory return laws from [Agent30](../agent30-429-odd-corridor/README.md) cover selected nearby corridors, and the [original raw halting criterion](../agent32-429-raw-parent/README.md) identifies the exact C/01 gate. An authentic source-connected exclusion of that gate would establish #429 nonhalting. No such exclusion or real blank-root halt witness is established here.

These results concern a precisely delimited prepared-tape mechanism and an empirical grammar hypothesis. Their external novelty and any implication for the numerical value of BB(6) remain unestablished.
