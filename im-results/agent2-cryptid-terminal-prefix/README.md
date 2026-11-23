# Cryptid D: 64 kernel-certified terminal right-prefix cylinders

**Status (2026-11-23):** a genuinely source-checked, *intermediate* theorem about prepared boundary configurations. The authentic blank-tape orbit has **not** been shown to enter this family, so this work neither decides Cryptid D nor determines BB(6). External priority/novelty has not been established. The mathematical certificate remains under `im-results/`, not `results/`.

## Statement

Use the original six-state, two-symbol D table
`1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`, with A=0,...,F=5 and tape bits 0=false, 1=true. An E-boundary configuration scans **0** at absolute coordinate zero, has the left-neighbor word (nearest first)

`00(10)^m11` with `m >= 3`,

and has the right-neighbor word (nearest first)

`1011011 w y`,

where `y` is **any finite Boolean word**, followed by the usual infinite blank tape. For each `w` in a fixed, explicit **prefix-free set of 64 words of length at most 12**, the machine reaches state F scanning a 1, with no defined next instruction, after exactly `t(w)` primitive machine transitions. The certified `t(w)` range is **74 through 177**, and the right-tail independence is proved for all `m >= 3` and all `y` (no length bound).

This is an infinite family of configurations, *not* merely 64 isolated finite simulations. The corresponding product cylinders have prefix-free Bernoulli measure `1227/4096` relative to independent uniform right-hand words after the fixed `1011011` prefix. This measure is a combinatorial property of the table, **not** the probability of entering the family from the blank tape.

## Lean theorem and trust

Source: [TailWindowPrefix.lean](../agent32-cryptid-padding/TailWindowPrefix.lean), importing Agent32's previously accepted [TailWindowCore.lean](../agent32-cryptid-padding/TailWindowCore.lean).

- `prefixTable` is the explicit list of 64 pairs `(w,t)`, with pairwise non-prefix initial words; word lengths are 3:1, 5:2, 6:2, 7:3, 8:6, 9:6, 10:11, 11:14, 12:19.
- `prefixTable_checked` is one computed **Lean proof**, not a simulator assertion: for each listed pair it proves positive time and `haltCheckWord t w = true`. The certificate examines the actual raw transition table and the entire finite path within window `[-5, 7 + |w|]`.
- `initialWordEqOn` proves that the local finite-window tape and the actual alternating-left tape with an arbitrary appended right word agree on the entire audited interval.
- `halts_with_arbitrary_suffix` transports certified finite paths by the previously proven all-step `runEqOn` and establishes that the resulting F/1 head is truly terminal.
- `all_prefix_table_halting` combines all of this for **every** `(w,t)` in `prefixTable`, every eligible left-stack length, and every arbitrary right suffix.
- Lean 4.36.0-rc2 [manual CI **45264135125**](https://github.com/FlareZ123/bb6/actions/runs/45264135125) **passed** on 2026-11-23. `#print axioms prefixTable_checked` reports only `[propext]`; `#print axioms all_prefix_table_halting` reports `[propext, Classical.choice, Quot.sound]`. Neither uses `sorryAx` nor `native_decide`. Run with the existing `agent32-cryptid-padding.yml` manual target `tail_prefix_cylinders`.

These theorems certify a **prepared E-boundary**, not the full root. In particular, merely knowing that the enormous upstream TM62 `A(3^108 k+C,[])` halting class exists does not license appending arbitrary right tails to its 107 symbolic reduction. A direct attempt to replace every intermediate source `A(…,[])` checkpoint by `A(…,ls)` in [SuffixParametricPrefix.append.lean](../agent32-cryptid-padding/SuffixParametricPrefix.append.lean) **failed to compile** (manual CI 45262562151); it is not a theorem and its hypothesis is not currently established. Do not splice its draft conclusion into the halting proof.

## Independently source-checked unbounded E scanner and exact first halt (23 November 2026)

An additional, genuinely **all-parameter** source result closes a different terminal branch rather than merely enumerating finite prefixes. For every `q >= 0`, any physical E/0 configuration with immediate left cells `001`, arbitrary further left tail `L`, right-neighbor pattern

```
(10)^q 1101101100 y
```

and arbitrary right tail `y`, reaches the original finite-list machine's frozen state 6 after exactly `73 + 2q` raw steps. The six-state undefined F/1 instruction occurs one transition earlier, at `72 + 2q` steps. The source-level proof in [AllQ1101101100.lean](./AllQ1101101100.lean) decomposes the run into a 4-step E-to-A prelude, a **2q-step scanner proved by induction**, a 3-step A-to-E trigger, and the **previously certified** arbitrary-tail 66-step `BB6.CryptidEHalt.e_halt_66`. Neither q nor either tail length is bounded. In [AllQFirstHalt.lean](./AllQFirstHalt.lean), the exact predecessor is proved F scanning 1 and frozen absorption rules out **all earlier** frozen-halting states.

Crucially, this is also connected to the **original F0 section** by the unchanged source-certified `CryptidBoundary.prefix_E`. For every `k,q >= 0` and arbitrary binary `y`:

```
I_(3k+4)( 0 (10)^q 1101101100 y )
  --[12k²+41k+106+2q raw transitions]-->
frozen halting state 6
```

Theorem `BB6.Agent2AllQE1101101100.full_E_all_q_halt` in [AllQSourceFeeder.lean](./AllQSourceFeeder.lean) gives the full conditional section-to-halt connection. Theorem `full_E_all_q_exact_first_halt` additionally proves that the displayed time is the **first** frozen halt from the section, with no earlier frozen state. In particular, this is not a bound extrapolated from q=0,1,... samples.

**Formal acceptance:** manual source-restored [CI 45267507107](https://github.com/FlareZ123/bb6/actions/runs/45267507107) compiled the SHA-checked original `Boundary.lean`, `EHaltCylinder.lean`, and all three new modules using Lean 4.36.0-rc2. `#print axioms` on each substantive theorem reports only `[propext, Quot.sound]` (some local finite lemmas use only `[propext]`); no `sorryAx` or `native_decide`.

The source-connected theorem adds the formerly unhandled `E_all_q_1101101100_halt` branch to the conservative [root-language macro interpreter](../agent37-root-language-pilot/macro_engine.py). That engine's halt-branch cost is `12k²+41k+105+2q` **successful** transitions, one less than the frozen state entry as required by its existing convention.

The missing root question is unchanged: neither the original blank orbit nor all of its exceptional successors has been proved to enter or exclude this family. The two families here are independently useful conditional halting classes; neither is an actual blank-machine decision. More trace enumeration or a further packed suffix extension would be less relevant than proving a complete physically exact root-language invariant, especially through the outstanding E/regular reset corridors.
