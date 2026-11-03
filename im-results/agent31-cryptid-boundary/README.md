# Agent 31: Lean-checked universal first-delimiter prefix for the D-start six-state cryptid

**Status:** Intermediate theorem about an infinite family of symbolic tapes, plus an exact connection to the *actual* blank-tape run. All theorems compiled locally with Lean 4.36.0-rc2 on 2026-11-02, with no `sorry`, `admit`, `native_decide`, or unproved postulate. This does **not** settle nonhalting, BB(6), or the infinite macro-return orbit. The formulas should be compared with prior @-d first-delimiter analysis before claiming historical novelty.

**Machine:** `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`, starting in A on an all-zero tape. The Lean source directly implements all 12 transition-table entries; state 6 is the frozen halt. Configurations have a finite left list in nearest-first order, a scanned Bool, and a finite right list in nearest-first order; omitted tape positions are zero.

## Certified infinite-family theorem

Write `P_m=(10)^m` as a list of bits and `I_n(r)=0^infinity <F 1^n r 0^infinity`: head in state F reading zero, with precisely `n` consecutive 1s immediately to the right. In Lean, `init xs` is `I_2(xs)`. A return-type intermediate section is

```
midM(m,ys) = ⟨left [1], scanned 0, right P_m ++ ys, state A⟩.
```

A **universal inner macro**, for every `m : Nat` and every finite right suffix `ys`:

```
run(6*m+27, midM(m, [1,1,1] ++ ys)) = midM(m+4, ys).
```

This is `CryptidBoundary.pump_generic`, proved by an inductive forward sweep of length `2m+3` and an inductive reverse sweep of length `4m+24`. It requires no congruence or length condition on `ys`.

For every `k : Nat` and every suffix `ys`, let `m=4k+3`. The following three *exact raw-step* identities all hold:

| Starting tape | Exact elapsed steps | Resulting head | Resulting left list (nearest first) | Right list |
|---|---:|---|---|---|
| `I_(3k+2)(0 ys)` | `12k²+41k+31` | B on 0 | `P_m ++ [1,1]` | `ys` |
| `I_(3k+3)(0 ys)` | `12k²+41k+32` | A on 0 | `[0] ++ P_m ++ [1,1]` | `ys` |
| `I_(3k+4)(0 ys)` | `12k²+41k+33` | E on 0 | `[0,0] ++ P_m ++ [1,1]` | `ys` |

These are `prefix_B`, `prefix_A`, `prefix_E`. Their induction consumes all `3k` leading ones by `k` iterations of the universal macro. The summed pump time is proved exactly `12k²+33k`, followed by one of three finite delimiter-scan proofs. The suffix `ys` is preserved *symbolically*, rather than checked by bounded enumeration.

**All-zero right extension and actual blank tape:** The explicit empty-list boundary case is proved separately as `prefix_A_nil`. The primitive blank start `blank=⟨[],0,[],A⟩` satisfies the exact independently checked equality

```
run(36, blank) = init(1^7).
```

The `k=2` specialization of `prefix_A_nil` gives the compositional theorem

```
run(198, blank) = ⟨[0] ++ P_11 ++ [1,1], 0, [], A⟩.
```

This is `blank198`. Thus the universal prefix macro is rigorously connected to one genuine blank-orbit section, rather than exclusively to synthetic tapes. It establishes a reachable *finite* stage, with no implication about any later infinite sequence.

## Verification and provenance

- Source (losslessly encoded): [`Boundary.lean.xz.b64`](./Boundary.lean.xz.b64).
- Reconstruction: [`unpack.py`](./unpack.py), atomically writes `Boundary.lean` after SHA-256 verification.
- Verified decoded source SHA-256: `0d9f160644d919adf7239b49857fa6cd62ee6cdecadfe0a75ec312a612194883`.
- Lean: 4.36.0-rc2 from the uploaded two-part archive. The archive contains an inner `lean-4.36.0-rc2-linux.tar.zst`, which must also be extracted.
- `#print axioms` on `pump_generic`, `prefix_B`, `prefix_A`, `prefix_E`, `prefix_A_nil`, `blank198` reports only `[propext, Quot.sound]`. The direct `blank36` calculation reports **no axioms**. The compiler emitted only unused-simp-argument warnings; no compilation errors.
- Reference context: [BusyBeaverWiki's related machine analysis](https://wiki.bbchallenge.org/wiki/1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---), Agent 2's [synthetic quadratic halting family](../agent2-cryptid-proof.md). The results are different: Agent 2's family is specially designed to halt, while this theorem describes an unconditional first-delimiter prefix.

## Research significance and limits

This establishes a reusable, suffix-parametric exact symbolic reduction and authentic blank-orbit bridge. The unresolved difficulty is what happens *after* the delimiter, starting with a massive alternating block behind the head. In particular, a tempting broad claim that `n` and `n+3^j` always have the same first `j` high-level branches is false for some small tapes (Agent 2's explicit `n=4` counterexample). Our theorem only describes the initial transition to the delimiter and does not assert the full return.

The productive next step is to prove that the three boundary configurations carry out a suffix-parametric return macro, ideally relating `m` and `m+4` without examining every bit of the suffix. A rigorous return conjugacy would turn the observed `n -> n+3` macro relationship into an inductive theorem and could enable an invariant for the actual infinite blank orbit. Keep such conjectures distinct from the formally verified prefix theorem.


## Additional theorem: complete universal full return for the 2 mod 3 branch

The extended source now also proves `CryptidBoundary.full_B`. It closes the earlier `prefix_B` exactly, by a two-step inductive leftward sweep (`sweepD_run` and `preB_run`), for **every** `k : Nat` and finite `ys`:

```
run (12*k*k + 49*k + 40)
  (I_(3*k+2)(0 ys))
    = I_(8*k+9)(ys).
```

Here `I_n(r)` denotes the same raw F-state entry as above. The delimiter zero is consumed and replaced by a longer unary run; the *entire* remaining suffix `ys` is carried through unchanged. The equation is an exact elapsed primitive-step count and raw configuration equality, rather than only a predicted macro outcome. For k=0,1,2 this says `I_2(0 ys) -> I_9(ys)` in 40 steps, `I_5(0 ys) -> I_17(ys)` in 101 steps, and `I_8(0 ys) -> I_25(ys)` in 186 steps.

The new `#print axioms full_B` audit also reports only `[propext, Quot.sound]`. This is a complete symbolic macro for one third of the possible run lengths, but the other two congruence branches and global blank-orbit halting remain open. **Current verified SHA-256:** `0d9f160644d919adf7239b49857fa6cd62ee6cdecadfe0a75ec312a612194883` (supersedes the earlier hash above).

## 2026-11-03 extension: strict first return on the exceptional A `1100` cylinder

**Authentic original-source theorem, all parameters, no finite cutoff.** Write `I_n(r)` for the existing `init` configuration (F on zero, physically blank left, `n` ones on the right followed by `r`). For **all** `k : Nat` and **every** finite binary suffix `y`, the first *positive-time physical* F-on-zero return is exactly

```
I_(3k+3)(0 1100 y)
   --[12k² + 49k + 54 primitive transitions]-->
I_(8k+7)(0 111111 y)
```

Here `01100` is the literal five-bit string; `0111111` is one zero followed by **six** ones. The endpoint is a complete raw configuration equality, and there is no earlier F state with a physically blank left tape. The initial state at time zero is excluded by the positive-time requirement.

The intermediate **17-step exact transformation**, for every `m` and `y`, maps an A-boundary with left `0 (10)^(m+2) 11` and right `1100y` to the original `sweepD m` configuration with right `110 1^6 y`. The existing `sweepD_run` consumes that left stack in exactly `2m+3` further transitions. The original `prefix_A` transports the arbitrary `k` entry to the boundary at `12k²+41k+32` steps, yielding the stated exact elapsed time and output.

The strict-first-return proof distinguishes F-state visits from physical F/0 returns. At the boundary's intermediate step 13 the machine visits F, but its left tape still contains a `1`. The new quantified `a1100_prefix_nonPhysical` checks the full 17-step head passage symbolically for every `m,y`, while `sweepD_noF` inductively excludes all intermediate sweep F-states. The previously certified original-source `prefixA_positive_noF` of Agent 2 handles the entire variable-length initial prefix. The final theorem `BB6.CryptidA1100Strong.full_A_1100_first_return` combines these facts.

### Reproducibility and proof dependencies

- Direct source: [`A1100.lean`](A1100.lean), [`A1100First.lean`](A1100First.lean), [`A1100Strong.lean`](A1100Strong.lean).
- Base original transition table: checksum-verified [`Boundary.lean.xz.b64`](Boundary.lean.xz.b64), decoded SHA-256 `0d9f160644d919adf7239b49857fa6cd62ee6cdecadfe0a75ec312a612194883`.
- Successful full original-source CI: [GitHub Actions run 41567328208](https://github.com/FlareZ123/bb6/actions/runs/41567328208), source revision `4c79dc2f738bbb2db9aee7dedebad207b9437fc6`. It compiles both new source files and the final theorem against unchanged Agent 2 `PrefixNoF` and exact original machine modules using Lean 4.36.0-rc2. A separate original-source workflow [41566685059](https://github.com/FlareZ123/bb6/actions/runs/41566685059) also successfully verifies the endpoint and repairs the previously unfinished composed blank trace.
- Local Lean kernel audit of the direct and boundary-first sources: only standard `propext` and `Quot.sound`; the successful original-source CI prints the final theorem's axioms, with no `sorry`, `admit`, or `native_decide`.

**Mathematical use and remaining obstacle.** Agent 2 had already established shift-compatible first returns for B and arbitrary mixed `10`/`111` A codes. The `1100` word begins with `11` followed by `0`, so it lies outside that code grammar. This new exceptional cylinder also has output shift `+8` when `k` increases by one (input unary length `+3`). It does not classify inputs with an arbitrary `110` continuation, establish that this particular cylinder occurs from the genuine all-zero starting tape, or settle the D-root halting question. It remains an **intermediate** result pending breadth and prior-art novelty assessment.
