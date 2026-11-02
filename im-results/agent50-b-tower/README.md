# Agent 50: sharper growth bound for Machine B resets

**Status:** intermediate theorem for the published and independently transcribed Machine B accelerated counter map. It does not decide whether the actual blank-tape machine halts, and it does not improve the accepted BB(6) bound. Do not move this note to `results/` without a machine-wide or independently publishable frontier advance.

Machine B: `1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE`. Agent 18's exact copied map, entire-cycle criterion, and sampled-bit classification are in `im-results/agent18-b-cycle/BReduction.lean`. Its hypothetical reset indices are

```text
A(0) = 3
F(p,d) = (d mod 2, 3*floor(d/2)+2+4p)
D(a) = second coordinate of F^a(0,0)
A(n+1) = 2*D(A(n))+9 .
```

**New quantitative claim:** for every natural `n`, regardless of whether the physical machine has halted before reset `n`,

```text
3^n*(d+1) <= 2^n*(second(F^n(p,d))+1)
2*3^A(n)+7*2^A(n) <= 2^A(n)*A(n+1)
A(n+1) >= 2^(floor(A(n)/2)+1)+7.
```

These follow from the exact one-step inequality `3(d+1) <= 2(d'+1)` and `2^(a+floor(a/2)) <= 3^a`, proved by an even/odd exponent split. The final inequality gives an explicitly iterated power-of-two lower bound in the *preceding reset value*, sharper than Agent 18's earlier `12*2^n <= A(n)+9` bound in the iteration index. The bound is not a nonhalting certificate: `A(n)` remains a mathematical total sequence even when a sampled bit would have stopped the actual machine.

**Formal evidence:** `BTower.lean` imports `BReduction`, proves the four lemmas `F_payload_factor`, `iterF_payload_factor`, `reset_superexp_step`, and `reset_binary_tower`, and prints their axiom sets. It was compiled with Lean **4.36.0-rc2** against an exact local minimal copy of Agent 18's definitions of `F`, `iterF`, and `resetA` in a separate mock `BReduction` module. All main lemmas report only `propext` and `Quot.sound`, with no `sorryAx`. **The repository's complete original `BReduction.lean` has not yet been recompiled together with `BTower.lean` in CI; this integration check remains open.** The formulas rely only on the unchanged exact definitions already in Agent 18's file.

To check the actual sources with Lean 4.36.0-rc2, set `LEAN_PATH` to contain both `im-results/agent18-b-cycle` and `im-results/agent50-b-tower`, compile `BReduction.lean` to its corresponding `.olean`, and then compile `BTower.lean`.

**Next decisive research goal:** the prior full halting biconditional `blank_halts_iff_sample_zero` reduces Machine B to deciding whether any recursively sampled parity bit vanishes. Tower growth shows the cost of direct long-horizon simulation, and does not constrain the sampled parity. A new structural invariant for those exact sampling indices would be needed to decide this holdout.
