# H(7) tail-parametric growth loop

**Status:** exact standalone macro identity in the projected outer-stack successor. The earlier blank-root connection is withdrawn after correcting the source token normalizer. It is not a candidate blank-root nonhalting proof; no Lean-checked original-TM theorem is claimed.

## Entry into the loop

The previous version of this note claimed that the corrected root seed reached `H(7)` at outer index 21,926. That claim is withdrawn: the c=2 token-normalizer transition used in that chain was wrong. The source-corrected root instead reaches `CR(L=0^255 ++ [1],R=[33])` at macro 21,827 and `EL(L=[0],R=[0,546])` at macro 22,083. See [RootCorridorMacro.md](RootCorridorMacro.md) and [TokenNormalizerCorrection.md](TokenNormalizerCorrection.md).

The standalone state `H(7)` and the identities below remain valid as projected-system investigations, but their reachability from the blank root is open. The accelerated root seed is `DR(L=[0,0],R=[1])` at raw TM time 7 and reaches `Corr(3,3)` after 24 outer successors.

Set

```text
P = [0,0,1,0,19]
B = [0,0,0,2,0,0,0,2,0,0,0,16]
U = [0,0,0,12,0,0,0,12,0,0,0,12,0,0,0,2,0,0,0,0]
```

The exact 157-successor entry macro is

```text
S^157(H(7)) = CR(L=[1,0], R=P ++ B ++ U).
```

This is a state-level identity from `H(7)`; it does not describe the root state at macro 22,083, which is `EL(L=[0],R=[0,546])`.

## The 76-successor growth macro

For every finite list suffix `T`,

```text
S^76(CR(L=[1,0], R=P ++ B ++ T))
  = CR(L=[1,0], R=P ++ B ++ B ++ T).
```

The 76-step path uses only the ordinary CR/EL/DL/DR outer clauses. It makes **zero** calls to `closeTokDR` and **zero** calls to `closeTokCR`. The suffix `T` is untouched: the path only inspects the fixed prefix `P ++ B`, and the output appends one additional copy of `B` immediately before `T`.

Consequently, defining

```text
C_n = CR(L=[1,0], R=P ++ B^(n+1) ++ U),  n >= 0,
```

gives `S^76(C_n)=C_(n+1)` for every `n ≥ 0`. Thus the projected outer-stack system has an infinite forward orbit from the state `C_0`, with the right list growing by 12 entries every 76 successors. The corrected blank-root trajectory is not known to reach `C_0` or `H(7)`.

## Source-normalizer correction and root reachability

The source-level correction is summarized in [TokenNormalizerCorrection.md](TokenNormalizerCorrection.md). In brief, `tok_EL_1` prepends one zero to the right stack. The former simulator omitted this update, so the old `closeTokDR([],0^2671)` output and all downstream root states were wrong. The corrected output is `CR(L=0^2711,R=[1])`, followed by the CR zero sweep described above. The old claim that the root enters `H(7)) is withdrawn.

The 76-step identity below does not call a token normalizer, so its standalone tail-parametric statement is unaffected. It must not be described as root-reachable.

## Reproduction and evidence

Agent 32 supplied the 157-step entry state and the tail-parametric 76-step derivation in [the H-phase communication](../../communications/agent12/20261122T031512Z_agent32-H-phase-76step-growth-macro.md).

I independently executed the checked-in array successor from `verify_root_corridor_macro.js` in the V8 runtime:
- `run(H(7),157)` exactly matched `CR([1,0],P ++ B ++ U)` in the prior projected-successor audit; this does not establish root reachability;
- the 76-step identity matched for suffixes `[]`, `[0]`, `[1]`, `[3,0,0]`, `[12,0,0,0,12,0,0,0]`, the actual `U), and `[7,5,3,1]`;
- an object sentinel appended as `T) survived the 76-step path unchanged.

These are executable checks of the projected array transcription. Agent 32 additionally reports a symbolic tail sentinel that throws if any transition reads or arithmetically inspects the suffix; it survived unchanged. Neither check substitutes for a Lean proof of the source correspondence.

## What this would establish if formalized

The tail-parametric identity is stronger than a long finite simulation: once proved against the source successor, it gives an infinite orbit from `C_0`. Since the 76-step loop avoids token normalization, its source proof should be approachable by composing the external `mode_CR_n_n_closed`, `mode_EL_n_n_closed`, `mode_DL_n_n_closed`, and `mode_DR_n_n_closed` lemmas (or their exact public equivalents). It does not settle the blank-root machine without a new reachability bridge.

The remaining obligations are:
1. Formalize the 157-step entry from `H(7)` and the 76-step tail-parametric identity against the actual source stack-mode definitions.
2. Find a new source-corrected route from the blank-root trace to `H(7)` or to another certified infinite-orbit family; the old c=2 route is invalid.
3. Prove that the stack projection preserves the relevant original TM execution and that no omitted exceptional/halting branch invalidates the lifted infinite path.

Until these are discharged, **do not claim the original TM is nonhalting**. The result establishes a standalone infinite projected-system orbit conditional on the source formalization, not BB(6) or the original-machine status.

## Raw TM cost of the 76-step macro

Agent 32 matched the 76 outer branch labels to the exact `execute n` lengths in the external #85 mode-closure proof. The branch accounting is:

| branch | occurrences | raw TM steps each | subtotal |
|---|---:|---:|---:|
| CR L=1, second=0 (`CR10`) | 8 | 5 | 40 |
| CR L=1, empty tail (`CR1e`) | 1 | 6 | 6 |
| CR L=1, second=1 (`CR11e`, `CR11`) | 2 | 16 | 32 |
| CR L=0 (`CR0`) | 13 | 2 | 26 |
| EL R=0 (`EL0`) | 16 | 2 | 32 |
| EL R>0 (`EL+`) | 12 | 1 | 12 |
| DL R=0 (`DL0`) | 8 | 6 | 48 |
| DL R>1 (`DL+`) | 4 | 4 | 16 |
| DR L=0, R>0 (`DR0+`) | 8 | 4 | 32 |
| DR L>0, R>0 (`DR++`) | 3 | 3 | 9 |
| DR L empty (`DRempty`) | 1 | 1 | 1 |
| **Total** | **76** |  | **254** |

Thus the 76-successor growth identity corresponds to **254 raw TM steps**. The two CR-second=1 branches both use the source's `execute 16` block; the path enters no token-normalizer branch.

Agent 32's proposed direct formalization target in the mirrored #490 module is the raw reachability theorem from

`evalStackCfg .CR_n_n [(1,0),(0,0)] (P ++ B ++ T)`

to

`evalStackCfg .CR_n_n [(1,0),(0,0)] (P ++ B ++ B ++ T)`

by `execute 254`, for arbitrary finite suffix `T`. This may avoid depending on private #85 `mode_*_closed` lemmas: prove the complete raw run in the #490 namespace using its public `execute` semantics and endpoint encodings. If one 254-step proof is unwieldy, split it into the 76 branch runs.

Source proof route: the #85 branch proof block is at lines 901–1065 of the external source file; branch counts and durations above were extracted from those `execute n` calls. This is a proposed Lean proof route, not yet a compiled theorem.