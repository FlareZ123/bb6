# Source audit: corrected token normalization and root continuation

**Status:** the token-normalizer corrections below remain source-derived, but the root continuation reported later in this file is WITHDRAWN. A separate outer-rule error was found: mode_DR_n_n_closed tokenizes both right-head 0 and right-head 1. The old simulator handled only right-head 0, so its root trajectory was already wrong at the first successor. See [DRHeadOneCycle.md](../agent48-cryptid-root-cycle/DRHeadOneCycle.md).

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

## Corrected root consequence

The blank-root stack seed is
`DR(L=[0,0], R=[1])`. The corridor prefix through
`Corr(263,2)` at macro 21,271 is unchanged. At macro 21,810 the root reaches
`DL(L=0^267 ++ [1], R=[1])) and invokes `closeTokDR`.

The corrected closure gives:

```text
macro 21810: DL(L=0^267 ++ [1], R=[1])
macro 21811: CR(L=0^271 ++ [1], R=[1])
macro 21827: CR(L=0^255 ++ [1], R=[33])
macro 22083: EL(L=[0], R=[0,546])
```

The c=2 corridor macro is consequently, for `r >= 8`,

```text
S^(2r+30)(Corr(r,2))
  = CR(L=0^(r-8) ++ [1], R=[33]).
```

For the root value r=263, this is the state at macro 21,827. The old
`Corr(3,4)` endpoint, and the subsequent root connection to `F(7)`,
`G(7)`, `H(7)`, and the H-phase growth loop, are withdrawn. Those later
identities may still hold as standalone projected-system statements, but
they are not established as root-reachable.

A source-equivalent persistent-list recurrence was executed for 1,000,000
macro-successor steps after the correction. It had one DR token closure, no CR
token closure, no token-halting branch, and no CR left-head-at-least-2 branch.
The left list remained in Z1 throughout that finite run. This is computational
evidence only; it is not a proof of an infinite orbit or a Lean theorem.

## Repository changes

- `fast_root_stack_sim.js`: corrected `tok_EL_1`, both CR `1,1` suffixes,
  and documented why the `v >= 3` `bounceDR` suffix is already correct.
- `verify_root_corridor_macro.js`: updated token regression expectations,
  corrected c=2 macro endpoint, and root continuation.
- `RootCorridorMacro.md`, `HPhaseGrowth.md`, and the folder README:
  withdrew the invalid root-to-H7 claim and recorded the corrected trajectory.

The updated checked-in Node harness has not yet been run under Node/CI after
these edits. Local shell execution returned a tool-level ClientError. The
formula checks and corrected root continuation were instead exercised in the
available V8 runtime using a direct source-equivalent transcription. No Lean
compile or axiom audit was performed.
