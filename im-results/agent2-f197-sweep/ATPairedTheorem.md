# F197: exact unbounded complementary-AT reset family

**Status: source-connected Lean theorem, not a blank-orbit/nonhalting proof.** The theorem and its exact primitive-transition costs hold for the literal six-state table `1RB0RE_1RC0LE_0RD---_0RE0RA_1LF0LB_1LA1LF`. Its arbitrary-length proof was accepted under Lean **4.36.0-rc2** at [run 46080673465](https://github.com/FlareZ123/bb6/actions/runs/46080673465), source commit `ffeb21f7bc1fd4c00f9e7f9e2b7293f3c93799a9`. The exported `F197.atp_family` has axioms only `[propext, Quot.sound]`; no `sorryAx`. It does not solve F197's blank-tape behavior or BB(6).

## The exact family

Use nearest-first left-run notation at the reset B boundary, right shortened run word `e` (terminal singleton). Let `A=(1,1)`, `T=(2,2)`, `P=AAT`, `e=(1,terminal)`, and `H(A)=AT`, `H(T)=AAT`.

Choose any `q≥0`, data `c₀,...,c_q ∈ {A,T}`, and arbitrary **nonempty run-aligned** left suffix `X` (its first physical bit is one). Define

```
Z(c₀,...,c_q) = c₀ (T c₁) ... (T c_q)
Φ(c₀,...,c_q) = A H(c₀) ... H(c_q).
```

Then the literal machine has a finite, entirely nonhalting sequence of exactly

```
156 + 68 q + 14 t
```

primitive transitions from reset `B(TAT Z AA X,e)` to reset `B(AAAT Φ X,e)`, where `t` is the number of T symbols among the `q+1` data. Every such return increases the explicit encoded left-tape bit-length by exactly **2**:

```
|TAT| + |Z AA| = 10 + 6(q+1) + 2t,
|AAAT| + |Φ| = 12 + 6(q+1) + 2t.
```

No claim that every reachable reset has this prefix is made. In particular, neither arbitrary suffixes after `TAT` nor an arbitrary leading `Pⁿ` lift has been proved covered by this theorem.

For `q=0`, the theorem contains two concrete exact identities:

```
TATAAA X → AAATAAT X        156 steps
TATTAA X → AAATAAAT X      170 steps
```

## Derivation and proof structure

1. **Initial carry insertion:** `B(TAT Y,e) → B(Y,u C e)` in 46 live transitions, with `u=(4,3)`, `C=(2,1)`. This is independent of the run-aligned `Y`.
2. **Recursive scanner:** each nonterminal A packet deposits the right token `t=(3,3)` in 8 steps; each T packet deposits `t A` in 18. The terminal AAA or TAA packet converts the remaining left prefix to `J=(1,2)` in 47 or 57 steps. The exact right-side carry decoder is represented by recursively defined `atpE/atpR/atpAcc` in `ATPaired.lean`.
3. **Recursive decoder:** each next-to-last data letter A/T is peeled by 60/64 steps, with **four distinct carried terminal peels** for the two possible final data letters. Final A/T bases decode in 63/67 steps, respectively.
4. Scanner and decoder are composed using the literal `run_add` law; the output is `AAAT Φ X` at terminal right `e`. Scanner cost is `47+8q+10t`, decoder cost is `63+60q+4t`, plus initial 46; hence the displayed exact formula.

The actual Lean declarations are `at_preconsume`, `at_term_A/T`, `at_peel_**`, `at_base_A/T` in [ATPairedCore.lean](ATPairedCore.lean); the eight guarded reusable scanner/decoder lemmas in [ATAlignedCore.lean](ATAlignedCore.lean); and `atp_scan`, `atp_peel`, `atp_decode`, `atp_family` in [ATPaired.lean](ATPaired.lean). They depend on Agent31's [Macro.lean](../agent31-f197-macro/Macro.lean) and [MacroExact.lean](../agent31-f197-macro/MacroExact.lean), which establish the exact macro-to-primitive source bridge. The first-tape-bit alignment assumptions are **essential**; proofs for an unconstrained arbitrary tape would require an unproved branch equality and must not be promoted.

## Research significance and remaining frontier

This resolves the formerly unclassified **TAT terminal followed by a paired-AA data word**, for any data length. The endpoint begins `AAA`, so an independently proved q=0 paired-AA reset would immediately append an `AAA X → P X` rewrite and produce `P T Φ X`, with another +2 tape bits. This suggests a positive-growth parser for the complementary AT carry state, rather than trying to assign one context-free output to every `AT` packet.

Open obligations are an induction grammar showing that the *authentic blank-tape reset orbit* always lies in covered safe prefixes; other terminal patterns and marker outputs `J/U/C`; and the full leading-`Pⁿ` lift. The theorem alone gives no upper/lower BB(6) bound beyond existing work.
