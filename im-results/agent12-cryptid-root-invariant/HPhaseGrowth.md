# H(7) tail-parametric growth loop

**Status:** exact macro identity in the projected outer-stack successor; candidate projected nonhalting proof. Not yet a theorem about the original Turing machine because the source-level correspondence of the projected successor and the finite root prefix has not been Lean-certified.

## Entry into the loop

The preceding corridor macros give the accelerated root stack seed

`DR(L=[0,0],R=[1])`

at raw TM time 7, then `Corr(3,3)` after 24 outer successors, and ultimately `H(7)` at outer index 21,926. The exact definitions of the `Corr/F/G/H` families and their finite prefix are in [RootCorridorMacro.md](RootCorridorMacro.md).

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

This puts the root stack seed into a tail-parametric growth region at outer index 22,083.

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

gives `S^76(C_n)=C_(n+1)` for every `nge0`. Thus the projected outer-stack system has an infinite forward orbit from the root seed, with the right list growing by 12 entries every 76 successors.

## Reproduction and evidence

Agent 32 supplied the 157-step entry state and the tail-parametric 76-step derivation in [the H-phase communication](../../communications/agent12/20261122T031512Z_agent32-H-phase-76step-growth-macro.md).

I independently executed the checked-in array successor from `verify_root_corridor_macro.js` in the V8 runtime:
- `run(H(7),157)` exactly matched `CR([1,0],P ++ B ++ U)`;
- the 76-step identity matched for suffixes `[]`, `[0]`, `[1]`, `[3,0,0]`, `[12,0,0,0,12,0,0,0]`, the actual `U), and `[7,5,3,1]`;
- an object sentinel appended as `T) survived the 76-step path unchanged.

These are executable checks of the projected array transcription. Agent 32 additionally reports a symbolic tail sentinel that throws if any transition reads or arithmetically inspects the suffix; it survived unchanged. Neither check substitutes for a Lean proof of the source correspondence.

## What this would establish if formalized

The tail-parametric identity is stronger than a long finite simulation: by induction it proves an infinite orbit of the projected stack successor. Since the 76-step loop avoids token normalization, its source proof should be approachable by composing the external `mode_CR_n_n_closed`, `mode_EL_n_n_closed`, `mode_DL_n_n_closed`, and `mode_DR_n_n_closed` lemmas (or their exact public equivalents).

The remaining critical obligations are:
1. Formalize the 157-step entry from `H(7)` and the 76-step tail-parametric identity against the actual source stack-mode definitions.
2. Certify the finite blank-root-to-stack-seed prefix and all preceding corridor macros in the same source semantics.
3. Prove that the stack projection preserves the relevant original TM execution and that no omitted exceptional/halting branch invalidates the lifted infinite path.

Until these are discharged, **do not claim the original TM is nonhalting**. The result currently establishes a strong candidate infinite orbit in the projected stack system, not BB(6) or the original-machine status.
