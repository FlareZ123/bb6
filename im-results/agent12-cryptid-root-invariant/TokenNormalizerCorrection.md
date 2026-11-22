# Source audit: corrected token normalization (root lift withdrawn)

**Status:** the token-normalizer corrections and source branch distinctions below remain valid. However, the previously claimed root continuation is withdrawn because the #490 wrapper mirrors #85 and swaps L/R. The macro-21,810 token event below belongs to a synthetic unmirrored #85 trace, not the actual #490 blank-root trajectory. The actual #490 blank seed corresponds to #85 `DR(L=[1],R=[0,0])` and has an immediate `tok_CR_1_0_closed` event. See [ModeDRBranchAudit.md](./ModeDRBranchAudit.md) for the mirror correction.

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

The earlier withdrawal in this section was incorrect. The pinned `mode_DR_n_n_closed` theorem uses `rcases r1 with _ | r5`: only r1=0 enters a token branch; r1≥1 takes the ordinary DR/CR branch. The root seed therefore begins with the ordinary four-step transition to `DR([0],[1,0])`, and the source-transcribed root countdown/growth replay is recovered when the simulator uses `b === 0` for DR. See [ModeDRBranchAudit.md](./ModeDRBranchAudit.md) and [RootCountdownGrowth.md](./RootCountdownGrowth.md).

The token-normalizer formulas above are unaffected by this outer-mode correction. In particular, `tok_EL_1` must prepend a zero, the CR `1,1` suffixes remain as stated, and the `tok_EL_add3` / `tok_DR_zero` composition still consumes the leading zero before `bounceDR` begins.

## Repository changes

- `fast_root_stack_sim.js`: now simulates the actual #490 blank root by swapping stacks into #85 orientation for each successor; its long replay has not yet been run.
- `verify_root_corridor_macro.js`: checks #85-side projected branch/countdown/reset and growth macro candidates only; it does not establish blank-root reachability.
- `stack_system_sim.py`: retains the #85-side projected DR right-head split; do not treat its unmirrored root trace as the #490 blank trajectory.
- The folder README and current proof target are [README.md](./README.md) and [RootCountdownGrowth.md](./RootCountdownGrowth.md).

The updated checked-in Node harness has not yet been run under Node/CI after
these edits. Local shell and Python execution returned tool-level errors. The
projected formula checks were exercised in the available V8 runtime using a
direct source-equivalent transcription. No Lean compile or axiom audit was
performed.


## Synthetic #85 token event and raw-step count (not blank-root)

This synthetic #85 event is `closeTokDR([],0^267 ++ [1])`. It is reached at macro 21,810 from `DL(L=0^267 ++ [1],R=[1])` in the unmirrored projected trace; the DL branch's initial `tExecute 4` enters the token closure. The source lemmas then give:
- 267 `tok_DR_zero` applications at 4 raw steps each;
- one `tok_DR_1_nil_28` at 28 raw steps;
- 268 `tok_EL_1` applications at 2 raw steps each;
- one `tok_EL_exit_zero` at 1 raw step.

Including the DL prefix, the event costs `4 + 267·4 + 28 + 268·2 + 1 = 1,637` raw TM steps and returns `CR(L=0^271 ++ [1],R=[1])`. The ordinary synthetic prefix before and after the event costs 64,565 and 595 raw steps respectively. These counts do not apply to the #490 blank root, and the former 66,804 blank-to-`D_0(540)` claim is withdrawn.
