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


## First token checkpoint from the blank-root stack entry

The #490 module's `init_reaches_nontrivial` target is
`evalStackCfg .DR_n_n [(0,0),(0,0)] [(1,0)]`.
Because `evalStackCfg` swaps the list arguments for the `DR_n_n` constructor, the corresponding #85-oriented `cfg_DR_n_n L R` has
[
L=[(1,0)],\qquad R=[(0,0),(0,0)].
]
In the first applicable branch of `mode_DR_n_n_closed`, the proof takes a three-step `texecute 3` prefix to
[
\operatorname{tok\_CR}([1,0],[(0,0)],[0]).
]
This is an exact token-system checkpoint in the closure proof for the authentic blank-root entry. It is not an inferred simulation.

The external halting-cylinder input has a separate local token representation, with an important state-map adjustment. For (C\equiv1\pmod3), (m=4(C/3)-1), its first `step_An_1101` intermediate is E in #490. The DeepMind state map sends #85 B to #490 E, so this is not a #85 `tok_EL` state. Since the suffix is empty, the scanned symbol is blank 0; #490 E0 writes 0, moves left, and enters C. After that one raw step, the tape is exactly
[
\operatorname{tok\_CR}([0]\; ++\; \operatorname{replicate}(m,1),[(1,0)],[]).
]
The left-list equality follows from `encTokens` and blank-extension equivalence; see `ASectionStackEncoding.md` for the derivation.

Thus the blank-root reduction and the external halting-cylinder proof both enter the same DeepMind token subsystem, but at very different token states. A precise reachability problem is now visible: determine whether the root's closed-stack/token evolution from `tok_CR [1,0] [(0,0)] [0]` ever reaches the halting token state associated with the cylinder (or another halting token state). No such reachability is established here.


## First root stack successor and short macro-prefix

The first root token closure can be simplified directly from the source proof. For
`tok_CR [1,0] [(0,0)] [0]`, `bounce_CR` consumes the right-list `[0]), then its empty-list case with accumulator value (2) returns the E-token state with (K=[1,0]) and right list ([0,0,1]). The `bl_terminates_le` proof applies `tok_EL_1` and then `tok_EL_exit_zero`, yielding the first outer stack successor:
[
\mathrm{CR}\;
L=[(0,0),(0,0),(1,0)],\qquad R=[(1,0)].
]
This is a derivation from the displayed `bounce_CR` and `bl_step_macro_len` cases, not an independent simulator result.

The next six outer mode transitions are explicit in `mode_CR_n_n_closed`, `mode_EL_n_n_closed`, and `mode_DL_0_n_closed`:
[
egin{aligned}
\mathrm{CR}([0,0,1],[1])
&\xrightarrow{2}
\mathrm{CR}([0,1],[3])
\xrightarrow{2}
\mathrm{CR}([1],[5])\\
&\xrightarrow{6}
\mathrm{EL}([0],[0,8])
\xrightarrow{2}
\mathrm{EL}([0,0],[8])\\
&\xrightarrow{1}
\mathrm{DL}([0,0],[7])
\xrightarrow{4}
\mathrm{DR}([0,0],[1,5]).
end{aligned}
]
Here each list entry abbreviates a pair ((a,0)), and the labels over arrows are the exact raw-step counts from the Lean `execute` blocks. These checkpoints provide a compact regression prefix for any executable implementation of the closed-stack successor relation.


The #85-to-#490 state relabelling is (f=[5,4,2,0,1,3]) (with directions mirrored). In particular, #85 D maps to #490 A at the root stack mode, #85 B maps to #490 E at the cylinder's intermediate state, and #85 C maps to #490 C at both token checkpoints. This is why the cylinder must take the E0 step before it becomes a #85/DeepMind `tok_CR` configuration.


An experimental transcription of the outer mode successor and token normalizers is now at [`stack_system_sim.py`](./stack_system_sim.py). Its first root token closure and six following mode successors were reproduced by a JavaScript prototype against the Lean-derived prefix above. The Python file itself was not run because the local container shell returned `ClientError`; no claims are made about longer trajectories until it is executed and compared against the source proofs.


## Initial-configuration transport caveat

The root checkpoint above is derived from DeepMind's own `init_reaches_nontrivial` theorem. The #85/#490 transition-table isomorphism alone does not prove that DeepMind's `init []` is definitionally the same initial tape/head convention as this repository's D0 root adapter. Before using the stack checkpoint as a formal bridge to the standard BB(6) blank-root trajectory, explicitly compare the initial state, blank symbol, and left/right/head conventions in both libraries. No independent raw replay of this cross-library prefix was completed here. The cylinder-side E0-to-`tok_CR` tape identity is a separate local derivation and is unaffected by this caveat.
