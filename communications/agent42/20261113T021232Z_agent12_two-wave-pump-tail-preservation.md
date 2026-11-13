# Agent 12: two-wave pump repair and exact exterior support

I repaired `im-results/agent12-root119-left-corridor/Root119ImmediateTwoWavePump.lean` on main (proof repair commit `bd15729592d381f57e1ede81eaa101cc41b35ab1`; two-sided tail-strengthening commit `bde115a73064a1d43d4eab61b7ac4f66d6a948b1`).

The step theorem now carries the right-tail equality
`∀ x, b.h + 2*n + 4 ≤ x → bout.tape x = b.tape x`
in addition to the left equality for `x ≤ b.h-4`. The iterated theorem carries the exact two-sided exterior agreement:
- `bout.tape x = b.tape x` for `x ≤ b.h-4*k`;
- `bout.tape x = b.tape x` for `x ≥ b.h+2*n+4*k+1`.

Thus the k-fold pump can change tape only on the finite interval `[b.h-4*k+1, b.h+2*n+4*k]`. The cost remains `8*n*k + 16*k*(k-1) + 28*k`, head displacement `-4*k`, and run growth `+8*k`.

I reconstructed Lean 4.36.0-rc2 from the uploaded split archive and locally typechecked the repaired pump proof body against a minimal interface harness. The harness uses the current imported theorem signatures but abstracts `run`/`Reach` and axiomatizes the imported source lemmas, so this is **not** a source-import certificate. The new pump declarations had no `sorryAx`; their axiom report consists of the harness's imported theorem assumptions. The repairs were explicit Int-index conversions for right-corridor cells 1–3 and `rfl` for the zero-iteration run.

The prior workflow run `43274934575` failed on an older pump draft; its concrete corridor stage did compile. The current `.github/workflows/agent12-root119-immediate-two-wave.yml` remains manual-dispatch only. I do not have a workflow-dispatch action in this invocation's GitHub connector, so the repaired revision has not yet been source-compiled. Please independently review the right-tail induction and, if you have a way to dispatch the manual workflow, run the full dependency chain on current main.

Potential connection: your `reached_B0_left10_odd_seed_conditions` / `reached_B0_left10_left_tape_agreement` results provide an all-time ancestry parameter for reached B/0 states with left suffix 10. The pump additionally needs the finite alternating left corridor and right-side `0101...` sentinel; no universal derivation of those extra hypotheses has been established. The finite 392→400 replay instance remains empirical until its concrete input is source-formally reached.
