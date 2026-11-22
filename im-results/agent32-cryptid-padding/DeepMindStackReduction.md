# Independent Cryptids stack reduction for #490

**Status:** external formal reduction, not a resolution of the machine's halting question.

The public Google DeepMind repository [`google-deepmind/cryptids`](https://github.com/google-deepmind/cryptids) contains a formal closed-stack reduction for the exact six-state machine used here:

- Target module: [`M_1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LEHHH.lean`](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/Accelerations/M_1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LEHHH.lean)
- The proof obtains the reduction by state relabelling and left/right reflection from [the #85 module](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/Accelerations/M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean).
- Toolchain: `leanprover/lean4:v4.35.0-rc4`.
- Mathlib revision in its manifest: `7c2f1a3e3c2e0c7a5b11aefc28fbcab5a7f24f5b`.

The target module's `has_stack_reduction` theorem supplies a `HasStackReduction` witness for #490. Its `init_reaches_nontrivial` theorem proves a seven-raw-step blank-tape entry into
[
\operatorname{evalStackCfg}\;\mathrm{DR\_n\_n}\;
  [(0,0),(0,0)]\;[(1,0)].
]
Under the module's `evalStackCfg` and `encLeft/encRight` definitions, this is a D-mode configuration with left encoding `1010` and right encoding `011`.

## Abstract system

The #85 module defines a `ClosedStackSystem` with four modes:
`CR_n_n`, `EL_n_n`, `DL_0_n`, and `DR_n_n`.
A pair `(a,b)` is encoded as a unary block of (a+1) ones followed by a zero separator; the separator length is fixed because the system's `maxSep` parameter is (1). The second coordinate is therefore invisible in the tape encoding, although the Lean transition proofs still carry it.

The closure theorem `stack_system_closed` proves that every configuration in the abstract stack system has a finite positive run to another stack-system configuration or to a halting configuration. Its mode-specific proofs are explicit case analyses on the top entries of the two pair stacks. The internal token subsystem includes `tok_CR`, `tok_DR`, and `tok_EL`; for example, `tok_CR_add2_halts` gives a halting case when the relevant CR token list begins with a counter at least two.

This is a genuine alternative representation of the same unresolved problem. It does **not** prove that the blank-root stack trajectory reaches the halting case, nor that it avoids it. The external 108-step (3)-adic halting cylinder has not yet been connected to a concrete stack-system orbit in this repository.

## Research value and next steps

1. Treat the seven-step stack entry as an independent formal root checkpoint, alongside the existing D0/F0 and external A-section checkpoints.
2. Derive an explicit deterministic stack-step interpreter from the four `mode_*_closed` case analyses and the terminating token routines. Validate it against the raw six-state machine on short prefixes.
3. Express the external A-section residue/cylinder data in the pair-stack representation. The likely useful correspondence is between unary counter blocks and the ((01)^q1^b) suffix language, but the head-boundary convention must be proved rather than guessed.
4. Use the resulting stack dynamics to search for a root invariant or a route into the known halting cylinder. Do not mistake the existence of a closed stack reduction for a proof of nonhalting.

The external repository uses Lean 4.35.0-rc4, while this repository's local target is Lean 4.36.0-rc2. Its files are therefore a mathematical reference, not a directly importable dependency without a deliberate port/rebuild.


## Run-length view of the token system

The definitions in the #85 module make the stack encoding more concrete:

```lean
encTokens (k :: K) R3 = 1^k 0 encTokens K R3
encRightNat (a :: L) = 1^(a+1) 0 encRightNat L
```

and `encLeft ((d,b)::R)` is (1^{d+1}0^{1+b\bmod1}encLeft(R)=1^{d+1}0encLeft(R)). Thus the token lists are run-length encodings of unary blocks separated by single zeros. `encTokens` stores left-side token runs before the pair-stack tail; `encRightNat` stores right-side run lengths. This is structurally close to the alternating ((01)^q1^b) suffix language used by the external A-section model.

A plausible bridge is therefore a run-length map from an A-section's left alternating block and finite right suffix to the ((K,R3,L)) data of `tok_CR`, `tok_DR`, or `tok_EL`. The correspondence must account for the scanned cell and whether the separator zero belongs to the head or to the encoded side; simply matching the visible strings is insufficient. Proving that head-boundary convention is the key prerequisite before translating the 108-step cylinder.


## Correct root-parameter transport

The #490 module's \`init_reaches_nontrivial\` target is
\[
\operatorname{evalStackCfg}\;\mathrm{DR\_n\_n}\;
  [(0,0),(0,0)]\;[(1,0)].
\]
There are **two** argument swaps in the definition chain:

- the #85 base \`evalStackCfg\` maps \`DR_n_n,L,R\` to \`cfg_DR_n_n R L\`;
- \`ClosedStackSystem.mirror\` defines the transported \`evalStackCfg m L R\` as
  \`mirrorCfg f (W.evalStackCfg m R L)\`.

The swaps cancel. The underlying #85-oriented configuration is therefore
\[
\mathrm{cfg\_DR\_n\_n}\;
  L=[(0,0),(0,0)],\qquad R=[(1,0)],
\]
not the reversed \`L=[(1,0)], R=[(0,0),(0,0)]\` stated in the earlier draft.

This changes the first applicable case of \`mode_DR_n_n_closed\`. Here the
first entries are \(a_1=0\) and \(r_1=1\), so the proof takes its
DR-to-DR branch, not the \`tok_CR_1_0_closed\` branch. Its four-step
\`execute 4\` prefix gives
\[
\mathrm{DR}\;L=[0],\quad R=[1,0]
\]
at raw time 11. The next DR case gives
\[
\mathrm{DR}\;L=[],\quad R=[1,0,0]
\]
at raw time 15. No root \`tok_CR [1,0] [(0,0)] [0]\` checkpoint occurs at
raw time 10; that checkpoint came from the reversed parameter interpretation.

## Corrected blank-root stack prefix

Lists below abbreviate pairs \((a,0)\). The raw times are measured from the
standard state-A blank start; time 7 is the formal \`init_reaches_nontrivial\`
entry. The outer macro checkpoints obtained by applying the source mode rules
are:

| Raw time | Mode | \(L\) | \(R\) |
|---:|---|---|---|
| 7 | DR | [0,0] | [1] |
| 11 | DR | [0] | [1,0] |
| 15 | DR | [] | [1,0,0] |
| 16 | EL | [0] | [1,0,0] |
| 17 | DL | [0] | [0,0,0] |
| 23 | EL | [0,1] | [0,0] |
| 25 | EL | [0,0,1] | [0] |
| 27 | EL | [0,0,0,1] | [] |
| 28 | CR | [0,0,0,1] | [0] |
| 30 | CR | [0,0,1] | [2] |
| 32 | CR | [0,1] | [4] |
| 34 | CR | [1] | [6] |
| 40 | EL | [0] | [0,9] |

The first seven successor states (times 11 through 27) are the regression
prefix in \`stack_system_sim.py\`. The subsequent checkpoints provide a
longer cross-check against the raw transition table. The Python interpreter
has not been run in this invocation because the local shell returned
\`ClientError\`; an independent JavaScript transcription of its successor
rules was executed and matched these stack configurations against raw
six-state simulation.

## The 36-step D0 checkpoint is an interior macro point

The repository's source-certified theorem
\[
\operatorname{run}\;D0\;36\;(\operatorname{blank}\;0)
  = \operatorname{F0Pure}\;9\;(-6)
\]
is not a competing endpoint for a first outer stack successor. It is an
interior raw configuration in the six-step CR-to-EL macro from the time-34
state \(\mathrm{CR}([1],[6])\) to the time-40 state
\(\mathrm{EL}([0],[0,9])\). At time 36 the raw machine is in state F with
head \(-6\) and ones exactly on \([-5,3]\), which is the stated
\(\operatorname{F0Pure}\;9\;(-6)\) configuration.

Thus the former C-versus-F discrepancy at raw time 36 was caused by the
wrong root stack parameters and the wrong claim that time 36 was the first
outer successor. The corrected stack prefix and the repository's D0 root
checkpoint agree along one raw blank-root orbit. DeepMind's \`init []\` and
the repository's \`blank 0\` both denote state A with an all-blank tape.
The existing \`TM62MathlibD0Adapter.lean\` supplies the signed-coordinate
tape map; a direct cross-library initial-configuration lemma still needs
compilation, but there is no longer a conceptual different-root explanation.

## Cylinder-side token target and remaining gap

The external A-section cylinder has a separate token-side derivation. For
\(C\equiv1\pmod3\), put \(m=4(C/3)-1\). The existing
\`ASectionStackEncoding.md\` records the cylinder-side E0 transition into
\[
\operatorname{tok\_CR}
  ([0]\mathbin{+\!\!+}\operatorname{replicate}(m,1),[(1,0)],[]).
\]
That cylinder encoding is **not** the blank-root checkpoint at time 7 or
the first root successor at time 11. The corrected outer-stack path must
still be advanced far enough to prove that it reaches this token state (or
another halting token state), or a genuine invariant must exclude it.
The closed-stack theorem alone proves neither outcome.

The #85-to-#490 state relabelling remains \(f=[5,4,2,0,1,3]\), with tape
directions mirrored. In particular #85 D maps to #490 A at the root, #85 B
maps to #490 E at the cylinder's intermediate state, and #85 C maps to
#490 C. Keep the cylinder-side E0-to-\`tok_CR\` statement separate from the
blank-root stack-entry derivation.
