> **Scope correction (2026-11-22):** The local token-normalizer equations may still be source-level facts, but their claimed occurrence at a particular blank-root macro index was derived from the withdrawn projected CR simulator. Do not use the old root token-event location as a reachability claim. See [the CR-branch correction](../../communications/broadcast/20261122T0813Z_agent12-critical-CR-branch-withdrawal.md).

# Source audit: corrected token normalization and restored blank-root connection

**Status:** the token-normalizer corrections and source branch distinctions below remain valid. The earlier root withdrawal was an evaluator-orientation error: #85's `evalStackCfg` swaps its arguments, and `ClosedStackSystem.mirror` swaps them again, so the reversals cancel. The actual #490 blank seed corresponds to #85 `cfg_DR_n_n [0,0] [1]`; the macro-21,810 DL token event is on the blank-root route. See [ModeDRBranchAudit.md](./ModeDRBranchAudit.md) and [RootCountdownGrowth.md](./RootCountdownGrowth.md).

## Pinned source

The comparison is against the DeepMind Cryptids source at commit
[`3647718b5df22e1a61462dec0376bd204526285a`](https://github.com/google-deepmind/cryptids/tree/3647718b5df22e1a61462dec0376bd204526285a),
file
[`BusyBeaver/BB6/Accelerations/M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean`](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/Accelerations/M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean).

The JavaScript normalizer stores the right suffix after the leading zero in
the source `tok_EL` configuration. Therefore a source output
`tok_EL K R3 (0 :: L_out)` is represented by `rightTail = L_out`.

## Corrections

### 1. `tok_EL_1` must prepend a zero

At source line 313:

```lean
tok_EL (1 :: K1) R3 L  ->  tok_EL K1 R3 (0 :: L)
```

The old `normalizeEL` branch removed the leading accumulator 1 but left
`rightTail` unchanged. This omitted one zero per consumed accumulator 1.
The corrected branch is:

```js
if (a === 1) {
  k = rest;
  rightTail = cons(0, rightTail);
  continue;
}
```

### 2. The two CR-token `1,1` suffixes were one zero too long

The source lemmas at lines 361 and 365 state:

```lean
tok_CR (k :: K1) R3 [1, 1]
  -> tok_EL (k :: K1) R3 [0, 0, 1]

tok_CR (k :: K1) R3 (1 :: 1 :: c :: L3)
  -> tok_EL (k :: K1) R3 (0 :: 0 :: (c + 2) :: L3)
```

After factoring out the implicit leading zero of the `tok_EL` contract, the
suffixes returned by `bounceCR` must be respectively
`[0,1]` and `[0,c+2] ++ L3`. The previous code returned one extra leading
zero in both branches. The persistent-list simulator and regression harness
now use the source-exact suffixes.

### 3. The proposed extra zero in the `v >= 3` branch is *not* a correction

The source lemma `tok_EL_add3` at line 321 preserves the complete right list:

```lean
tok_EL ((k + 3) :: K1) R3 L
  -> tok_DR (2 :: k :: K1) R3 L
```

However, the source proof immediately composes it with `tok_DR_zero` at line
329. The composition is explicit in `bl_step_macro_len` at lines 806–808:

```lean
ReachesPlus.trans
  (tok_EL_add3 k' K1 R3 (0 :: L))
  (tok_DR_zero (k' :: K1) R3 L)
rcases bounce_DR R3 (1 :: k' :: K1) L with ...
```

Thus `tok_DR_zero` consumes the leading zero before `bounce_DR` begins.
The existing JavaScript call

```js
bounceDR(r3, cons(1, cons(a - 3, rest)), rightTail)
```

already represents the composed source path: the accumulator includes the
new 1 and the right suffix is the tail after the consumed zero. Passing
`cons(0, rightTail)` would apply `tok_DR_zero` twice. The previous audit
suggesting that extra zero is therefore rejected.

## Exact DR-token closure formulas on Z1

Write `Z1 = 0^*(epsilon | 1)`, and let `bump(r)` increment the head of the
right context (or create `[1]` if it is empty).

The source lemmas `tok_DR_zero` (line 329), `tok_DR_nil_8` (line 325),
`tok_DR_1_nil_28` (line 333), `tok_EL_1` (line 313), and
`tok_EL_exit_zero` (line 303) give:

```text
closeTokDR(r, 0^n)     = CR(L = 0^(n+1) ++ [1], R = bump(r))
closeTokDR(r, 0^n ++ [1])
                       = CR(L = 0^(n+4) ++ [1], R = bump(r))
```

For `0^n`, the DR bounce creates accumulator `1^n ++ [0]` and right
suffix `[1]`; the n applications of `tok_EL_1` add n zeros before the
final `tok_EL_exit_zero`. For `0^n ++ [1]`, `tok_DR_1_nil_28` supplies
the initial right suffix `[0,0,1]` after factoring out the implicit leading
zero, and the n+1 applications of `tok_EL_1` produce n+4 zeros in the final
CR left list. Both outputs lie in Z1.

## Root consequence under the correct outer DR rule

The evaluator composition is now checked explicitly: #490 `evalStackCfg .DR_n_n L R = mirrorCfg f (cfg_DR_n_n L R)`, because #85's own evaluator already reverses the arguments. The blank seed therefore begins with the ordinary four-step `DR([0,0],[1]) -> DR([0],[1,0])` transition. The DL right-head-1 token event occurs later, at projected macro 21,810. See [ModeDRBranchAudit.md](./ModeDRBranchAudit.md) and [RootCountdownGrowth.md](./RootCountdownGrowth.md).

The token-normalizer formulas above are unaffected by this outer-mode correction. In particular, `tok_EL_1` must prepend a zero, the CR `1,1` suffixes remain as stated, and the `tok_EL_add3` / `tok_DR_zero` composition still consumes the leading zero before `bounceDR` begins.

## Repository changes

- `fast_root_stack_sim.js`: uses the no-swap #85 `cfg_DR_n_n` transition on the #490 stack arguments; the evaluator reversals cancel.
- `verify_root_corridor_macro.js`: checks the source-transcribed blank-root-connected projected branch/countdown/reset and growth macros; it is not a Lean proof.
- `stack_system_sim.py`: its no-swap #85 `cfg_DR_n_n` trace has the correct stack-list order for the #490 root after the mirror cancellation.
- The folder README and current proof target are [README.md](./README.md) and [RootCountdownGrowth.md](./RootCountdownGrowth.md).

The updated checked-in Node harness has not yet been run under Node/CI after
these edits. Local shell and Python execution returned tool-level errors. The
projected formula checks were exercised in the available V8 runtime using a
direct source-equivalent transcription. No Lean compile or axiom audit was
performed.


## Blank-root-connected token event and raw-step count

This #490 blank-root event is `closeTokDR([],0^267 ++ [1])`. It is reached at projected macro 21,810 from `DL(L=0^267 ++ [1],R=[1])` in the no-swap `cfg_DR_n_n` trace; the DL branch's initial `tExecute 4` enters the token closure. The source lemmas then give:
- 267 `tok_DR_zero` applications at 4 raw steps each;
- one `tok_DR_1_nil_28` at 28 raw steps;
- 268 `tok_EL_1` applications at 2 raw steps each;
- one `tok_EL_exit_zero` at 1 raw step.

Including the DL prefix, the event costs `4 + 267·4 + 28 + 268·2 + 1 = 1,637` raw TM steps and returns `CR(L=0^271 ++ [1],R=[1])`. The ordinary prefix before and after the event costs 64,565 and 595 raw steps respectively. The stack-seed-to-`D_0(540)` total is 66,797 raw steps; including the seven-step blank entry gives 66,804 raw TM steps from the #490 blank tape.
