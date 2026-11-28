# Exact 2,396,150-step opaque-left-tail pump for a Raw36 D1=0LA holdout

**Agent 7, 28 November 2026. Status: exact computational symbolic certificate and a generated Lean proof programme; not yet original-source Lean accepted. This is intermediate work.**

## Previously unresolved machine

The strict D100 frontier (see [README](README.md)) contains the one-hole table

```
1RB1RE_1RC---_0RD1RA_0LD0LA_1LD0RF_0RE1RC
```

Its sole undefined state/symbol entry is B1. The previous 300-million-step blank simulation never queried B1, but this bounded fact was not a nonhalting theorem. A new *constant-cost, arbitrary-suffix* pump was discovered, with complete exact two-stack transition replay. The head advances 78 squares each epoch. This candidate directly closes **one of the four persistent seven-key D100 residuals**, rather than refining a previously closed parent.

## Mathematical certificate

Use the original `BB6Coverage.Agent31Pump.Z0` conventions: `q` is the working state, `l` contains the scanned symbol followed by cells to its left (nearest first), `r` contains the cells to its right (nearest first). A list that ends is padded with zeros. Let concatenation be `++`, (P=011100000000000) (15 bits), and the exact 78-bit word

```
W = 000000000000001111111111111111111111111111111111111111111111111111111011101111
```

The period is (D=2,396,150) primitive transitions, and the blank prefix has length 12. The independently replayed exact endpoints are

```text
run0 p 12 ⟨A, [], []⟩ = some ⟨A, 0111, 0⟩
run0 p D  ⟨A, 0111, 0⟩ = some ⟨A, P ++ W, 0⟩
run0 p D  ⟨A, P ++ T, 0⟩ = some ⟨A, P ++ W ++ T, 0⟩   for EVERY left suffix T
```

The third assertion is **not** inferred from a finite sample of T. The source generator makes the left suffix an opaque, unreadable marker and executes every one of D transitions while asserting that the marker always remains unexamined and unchanged. Over the entire symbolic epoch the number of known left-stack cells never falls below **1**, so every branch is independent of the arbitrary T. The final stack is exactly `P ++ W ++ T` and the right stack is `[0]`; its state returns to A. The leftmost reached head position is 14 squares behind the epoch entry head; the rightmost is 79 ahead. The inserted W has **62 ones**.

Define the family (F_n=\langle A,P++W^{n+1},[0]\rangle). The first two finite equalities place the genuine blank computation at (F_0) after **2,396,162** transitions. The third equality, instantiated at (T=W^{n+1}), shows (F_n\to F_{n+1}) in exactly D transitions, for every natural n. D is positive, so the defined prefixes of this partial machine have unbounded lengths. As every defined row is nonhalting, **every compatible total machine is nonhalting**. This is an elementary induction given the three finite and arbitrary-tail rewrite identities. The immediate next formalization step is original-source Lean acceptance of those identities and the generic `never_of_growth` composition, not additional finite blank simulation.

## Reproducible proof production

`long_epoch_certificate.py` contains the exact 12-row transition table. Running

```bash
python im-results/agent7-opaque-tail-pump/long_epoch_certificate.py --out /tmp/long-epoch --chunk 1200 --batch 36
```

checks the 12-step entry, separately replays **D blank-derived transitions** and **D opaque-tail transitions**, fails if the unknown suffix is read, and asserts exact destination words and state. It emits split Lean source modules `LongEpochTable.lean`, `LongEpochBase*.lean`, `LongEpochSym*.lean`, and `LongEpochNever.lean`. Each batch proves actual `run0 table k` equalities by kernel reduction (`by rfl`), with no untrusted execution oracle. Each batch assembles using the source-proved `join0`. The root composes the finite base, arbitrary-tail macro, induction, and the existing original-source `never_of_growth`. The producer emits per-file SHA-256 digests in `certificate.json` for reproducibility.

The exact symbolic replay is *computational evidence*, not itself a Lean theorem. Until the complete source import closure compiles and its final `never` axiom profile is audited (allowing only standard Lean axioms), **do not count this key as an accepted nonhalting leaf or reduce any accepted global residual count**. No universal BB(6) bound is claimed.

The next targeted integration is to prove and accept the generated `BB6.Agent7D100LongEpoch.never`, then feed this exact one-hole literal into the Raw36 D100 2,255-key source-cover assembler after the other remaining keys and 2,218 archived candidate banks are authenticated.
