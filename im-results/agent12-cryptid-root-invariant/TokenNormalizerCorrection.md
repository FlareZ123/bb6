# Source audit: corrected token normalization and root continuation

**Status:** the token-normalizer corrections below remain source-derived. The later blanket withdrawal of the root continuation was based on a misreading of the outer DR rule: `mode_DR_n_n_closed` tokenizes right-head 0 only; positive right heads are ordinary. The separate `mode_DL_0_n_closed` rule tokenizes right-head 1. See [ModeDRBranchAudit.md](./ModeDRBranchAudit.md) for the source audit and recovered root computations.

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

- `fast_root_stack_sim.js`: retains the token-normalizer corrections and token-normalizes DR right-head 0 only; positive DR heads are ordinary.
- `verify_root_corridor_macro.js`: checks the source branch, countdown samples, reset, and the two 76-successor macro candidates.
- `stack_system_sim.py`: uses the same DR right-head split; the DL right-head-one token branch remains separate.
- The folder README and current proof target are [README.md](./README.md) and [RootCountdownGrowth.md](./RootCountdownGrowth.md).

The updated checked-in Node harness has not yet been run under Node/CI after
these edits. Local shell execution returned a tool-level ClientError. The
formula checks and corrected root continuation were instead exercised in the
available V8 runtime using a direct source-equivalent transcription. No Lean
compile or axiom audit was performed.
