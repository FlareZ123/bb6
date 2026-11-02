# Agent 32: original-machine infinite-blank padding bisimulation

**Research status:** reusable original-source formal infrastructure, **intermediate**. It does not decide the Cryptid holdout, establish blank halting/nonhalting, or improve a Busy Beaver bound. No claim of external novelty.

## Problem

The original Cryptid six-state machine `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---` is encoded by Agent 31's verified original `CryptidBoundary.Cfg` with finite `l, r : List Bool`, scanned bit `h`, and state `st`. Lists are finite representations of semi-infinite tapes filled with zeros. Consequently, `xs` and `xs ++ replicate q false` may denote the **same physical tape** while remaining unequal Lean lists. A symbolic exact-return equality involving a terminal `false` cannot simply be substituted for a genuinely implicit blank suffix by `rfl`.

## Theorems

[`Generic.lean`](./Generic.lean) defines the infinite tape observation `bitAt xs i = (xs[i]?).getD false`; `TapeEq` equates every such bit. It proves for an arbitrary deterministic two-symbol transition table:

```lean
run_pad (delta : Nat → Bool → Option Instr) (n p q : Nat) (c : Config) :
  CfgEq (run delta n c)
    (run delta n ⟨c.left ++ List.replicate p false,
       c.bit, c.right ++ List.replicate q false, c.state⟩)
```

[`BoundaryPadding.lean`](./BoundaryPadding.lean) defines the **exact** Cryptid rule table, with F-on-1 entering the frozen state 6, and proves `source_step` and `source_run` as a semantic equality to Agent31's **unmodified raw machine**.

- `source_congr`: observationally equivalent source configurations remain equivalent after every finite raw-machine run.
- `source_pad`: any far-end all-zero padding on either tape half preserves physical evolution.
- `source_init_pad`: the original `CryptidBoundary.init xs` evolves equivalently to `CryptidBoundary.init (xs ++ replicate q false)` at all times.
- `source_init_halt_iff`: their exact finite-time halt-state-6 indicators agree for all `n,q,xs`.
- `source_chain`: any two exact-interval observational certificates can be composed, allowing physically equivalent but syntactically differing intermediate configurations.
- `source_transport`: exact symbolic macros transfer to all observationally equivalent start and finish configurations.

[`PaddedApplications.lean`](./PaddedApplications.lean) applies the existing source-verified `CryptidBoundary.full_E_pairs` theorem to a **genuinely implicit blank** at the right tape end, for all natural `k,q`. It proves:

```text
I_(3k+4)(0 (10)^q [implicit infinite blank])
  --[12k²+49k+50+4q raw steps, physically]--> 
I_(8k+5)(0 1^(2q+6) [implicit infinite blank])
```

The conclusion is `ObsEq` (infinite-tape semantics), not syntactic equality of the finite lists. This is a logically sound specialization of the existing macro; it is not a new return-word family.

## Reproducibility and trust

- Toolchain: Lean 4.36.0-rc2, standard kernel.
- SHA-verified original upstream `Boundary.lean` from `../agent31-cryptid-boundary/unpack.py`, whose recorded content hash is `0d9f160644d919adf7239b49857fa6cd62ee6cdecadfe0a75ec312a612194883`.
- Manual workflow: [`.github/workflows/agent32-cryptid-padding.yml`](../../.github/workflows/agent32-cryptid-padding.yml); it runs **only** via manual `workflow_dispatch`, never on commits.
- Original-source CI [41419395469](https://github.com/FlareZ123/bb6/actions/runs/41419395469) passed. The core `source_step`, `source_run`, `source_congr`, `source_pad`, `source_chain`, `source_transport` all have axiom audit exactly `[propext]`, with no `sorryAx`.
- The additional initial-padding and E-pairs specialization are in the later workflow run, whose exact success and axiom list should be checked independently before citing them as original-source verified.

## Why it matters and what it does not imply

This proves an all-time semantic representation invariant and eliminates the common misuse of syntactic tape-list equality when moving between explicit and implicit zeros. The `source_chain` combinator provides a principled route to an actual-blank forward certificate that uses existing unbounded exact macros with possibly different list padding. It **does not** provide a closed reachable-word invariant or prove that the actual blank orbit follows an infinite symbolic return sequence. Existing millions-section computational work by @-d still greatly exceeds the finite conditional itineraries in this repository.
