# BB429 authentic-blank halting equivalence: the raw B/001 gateway

**Current verified status (7 November 2026):** the machine `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA` halts from blank tape **if and only if** its genuine raw trajectory visits state B with tape bits `0,0,1` at the head and the next two cells to the right. The exact equivalence is original-source Lean-checked at [CI run 42321557497](https://github.com/FlareZ123/bb6/actions/runs/42321557497), commit `05b9001119d164bb209028657594c8a914da0d5d`. The earlier all-time F-entry and C-only predecessor theorems were separately source-certified in [CI run 42320830215](https://github.com/FlareZ123/bb6/actions/runs/42320830215), commit `c5a5634bd1b1e43ea4b0ff9c8db547ec038e3319`.

**The genuine blank-root reachability of the B/001 gateway is unresolved.** Consequently, the halting status of machine #429 and exact BB(6) remain open. The proof establishes a source-checked equivalent *raw local reachability question* and a forbidden immediate predecessor; it does not exclude the reachable fatal event or establish publication priority. This intermediate work remains in `im-results/`.

## Mathematical statements, all-time and exact

Write `M` for the literal exact target from [Agent1's verified rooted sparse physical frontier](../agent1-429-physical-frontier/BB429PhysicalFrontier.lean), `R_n` for the genuine `BB6Coverage.run M n blank`, and `h` for the head coordinate. The tape has the actual full two-way infinite Boolean semantics from `BB6Coverage.Frontier`.

The all-time raw predecessor theorem [`target429_D1_only_from_C0`](BB429FEntry.lean) establishes that any successful blank-root configuration scanning **D/1**, at any nonzero raw time, must follow **C/0** immediately. It follows because all incoming F instructions write zero and move left. Therefore every reachable F configuration has a zero immediately to the right of its head; the actual F/0 instruction moves right into D over that guaranteed zero. C/0 and F/0 are the only instructions entering D. The general lemma `safe_F` proves the geometric cell property for every machine having the same F-entry constraint.

The subsequent [`target429_D1_iff_B001`](BB429FatalB.lean) proves for **every** `n : Nat`:

```lean
(∃ z, run target429 (n+2) blank = some z ∧ readSlot z = (D,true)) ↔
(∃ b, run target429 n blank = some b ∧ fatalB b)
```

Here `fatalB b` is exactly `b.state = B`, `b.tape b.head = false`, `b.tape (b.head+1) = false`, and `b.tape (b.head+2) = true`. **Both directions** use the original raw table: B/0 writes one and moves right to C, C/0 writes zero and moves right to D, and D/1 halts. In the reverse direction, Lean proves B/0 is the only entry into C and C/0 the only reachable predecessor of D/1. It physically follows the tape writes, rather than inferring the next input from a speculative control path.

The global theorem [`target429_halts_iff_root_B001`](BB429FatalB.lean) additionally proves:

```lean
(∃ n, HaltsAfter target429 n) ↔
(∃ n b, run target429 n blank = some b ∧ fatalB b)
```

The initial two nonhalting transitions are separately checked, and the unique halting input is shown to be D/1 by exhaustive inspection of all twelve literal rows. For a B/001 event at successful-step index `n`, the halt is after `n+2` successful steps and the final attempted halt occurs at score `n+3`. This convention agrees with the original raw-machine `HaltsAfter` definition.

## Proof provenance

- [BB429FEntry.lean](BB429FEntry.lean) supplies `move_left_zero_right`, `safe_F`, `F0_successor_reads_zero`, `target429_F_entry`, `target429_F0_safe`, `target429_D_input`, and `target429_D1_only_from_C0`.
- [BB429FatalB.lean](BB429FatalB.lean) supplies the exact one-direction and bidirectional B/001 gate proofs and the globally quantified halting equivalence.
- [Manual source workflow](../../.github/workflows/agent32-429-raw-parent.yml) installs Lean 4.36.0-rc2, compiles unchanged original `Frontier`, `RayFinite`, `FrontierAudit`, `PhysicalTraceAudit`, `LassoTraceAudit`, the Agent1 #429 literal source, and these two new modules. The successful [full-source run 42321557497](https://github.com/FlareZ123/bb6/actions/runs/42321557497) inspected `#print axioms` output and rejected `sorryAx`. Local direct kernel compilation gave the standard axiom list `[propext, Quot.sound]` for the new final theorem.

## Frontier relationship and unresolved task

Agent6's [original Cryptids accelerator and 44/1024 necessary terminal masks](../agent6-harmonic429/README.md) and Agent1's [673/928 depth-20 inverse certificates](../agent1-429-262144-sieve/README.md) already provide substantially stronger **high-level necessary** reachability restrictions. The raw B/001 theorem is an exact reformulation at the literal machine-level, potentially useful for independent tape-language invariants. It may be implicit in existing source acceleration and no external novelty claim has been established. No historical holdout or BB(6) upper bound was decided.

An empirical raw simulation of 50 million successful steps observed every visited C/0 configuration at the rightmost head coordinate seen so far, so its right-hand neighbor was blank. This bounded observation motivated the geometric question whether **every** blank-root C/0 is at a fresh right frontier. No all-time proof is known, and finite evidence cannot establish it. An inductive invariant excluding the authentic B/001 pattern, or a true witness visiting B/001, would settle this machine. Future work should investigate unbounded right-tape structure rather than simply raising finite simulation limits.
