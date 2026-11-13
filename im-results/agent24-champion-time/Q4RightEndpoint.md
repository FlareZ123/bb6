# TM63 q4 suffix: full canonical endpoint candidate

**Status: uncompiled proof candidate; not a BB(6) result.** The source-level proof is now written through the complete q4 macro endpoint, but neither the strengthened prefix interface nor the combined suffix/endpoint module has passed the repository's manual original-source audit.

## Exact theorem candidate

`Q4RightEndpoint.lean` now contains:

- `q4_prefix_far_tail`: the strengthened Agent 6 right-facing stream implies a blank ray beyond the q4 word.
- `q4_suffix_right_word`: the 39+3*b suffix frame produces the exact complete right-facing word `s0RightFacing 0` and preserves the blank ray.
- `q4_suffix_left_word`: the complete left-facing output is the canonical word
  `d0pow b ++ d1pow 2 ++ (q4LeftFacing L n a).drop 1`.
- `q4_suffix_run_target_of_prefix`: composes the prefix and suffix runs, and identifies both infinite tape exteriors plus state/head with the next original-source `s1Config`.
- `oddRst2_q4_counted_source`: the resulting uniform counted source theorem.

The proposed theorem is, for odd `n < 2^L`:

```lean
run tm2 (71+12*a+3*b) (s1Config L n 2 a 0 b h) =
  some (s1Config L (n-1) 1 (a+b+2) (2^b-1) 0 (h+5+3*b))
```

This is a theorem statement with a proof body in the repository, **not yet a kernel-verified theorem**.

## Endpoint proof architecture

Let `g=h+10+3*b` be the suffix tail-frame origin and `H=g-5` its final head.

- **Right side:** Agent 6's complete q4 right-facing stream has length `9+3*b`, hence every farther input cell is blank. Agent 8's suffix frame writes the nine target cells and leaves the blank ray untouched.
- **Left side, first `3*b` cells:** the counted scan changes each three-one block to `001`. Read leftward from `H`, the output is periodic `001`; the four boundary cells supplied by the first-ten frame are `1,0,0,1`, completing the same periodic word.
- **Next six cells:** the first-ten frame marks every cell from `h` through `h+5`, giving `d1pow 2`.
- **Remaining left ray:** cells at and left of `h-1` are untouched by both suffix frames and the scan. Agent 6's prefix left-stream equality therefore supplies `(q4LeftFacing L n a).drop 1`.
- Agent 8's `q4SuffixTargetLeft` identity equates the combined word with the canonical target `s1LeftFacing`. The two pointwise half-tape results, final state/head, and `config_ext` identify the entire infinite tape.

This closes the exact source-run interface without assuming a finite tape or extrapolating a simulation. The proof still needs compilation and axiom audit.

## Authentic blank-root specialization

The kernel-checked root bridge gives:

```lean
run tm2 27959 blank = some (s1Config 3 7 2 6 0 63 29)
```

At `(L,n,a,b,h)=(3,7,6,63,29)`, the q4 macro candidate has cost `104+228=332` and target:

```lean
s1Config 3 6 1 71 (2^63-1) 0 223
```

Thus, **if the q4 theorem compiles**, composing it with the root bridge gives a 28,291-step original-source prefix to that next S1 state. Agent 48's simulator independently observed a 332-step endpoint at state 3/head 223 with 106 marked cells and support `[-10,232]`. The encoder gives the same count and support: `binDec 71 (2^63-1) = d0pow 63 ++ d1pow 8` contributes 87 ones; `markerWord 1`, `d0`, `binDec 3 6 = d1 ++ d0 ++ d0`, and `lh` contribute 2+1+5+5, so the left stream has 100 ones. `s0RightFacing 0` contributes six more. The left stream length is 234, placing its far edge at `223-233=-10`, and the nine-cell right stream ends at 232. This is an independent consistency check, not a proof that the 332-step run reaches the canonical target.

The target is a positive all-ones S1 counter. `im-results/agent48-counted-inc0/S1CountedInc0.lean` proposes a parity-complete counted decrement, and `S1CountedDrain.lean` composes it into an all-ones drain. The drain theorem applies at `(L,n,m,a,k,h)=(3,6,1,71,63,223)` and would take `s1Config 3 6 1 71 (2^63-1) 0 223` to `s1Config 3 6 1 71 0 (2^63-1) 223` in `6*4^63+42*2^63-804` moves. Conditional on both q4 and drain source proofs, the blank-root prefix through this drain would be `27959+332+(6*4^63+42*2^63-804) = 6*4^63+42*2^63+27487` steps. Both the q4 endpoint and S1 decrement/drain chain remain uncompiled candidates; this is not a certified lower bound or full halting score.

## Verification and remaining work

The original finite-interface q4 prefix passed CI 43334058991. The later strengthening that exports the full right stream is in commit `7369e2778204ed876a9cb8529981ac1f09ad9796` and has not yet been compiled. The expanded `Q4RightEndpoint.lean` is also uncompiled.

The last available full champion-root run, 43340804651 (failed job 131608321957), reached `Q4Suffix.lean` and failed at line 439: `rw [heq1]` could not match `h + 6 + 3 * 1` against the goal coordinate `h + 6 + 3 * ↑1` after `b=1`. The current file still contains this rewrite. The same log reports `q4_suffix_frame` depends on `sorryAx`; the source has no explicit `sorry`, so this is consistent with Lean's error recovery inserting a placeholder after the failed tactic. Agent 8 has been sent the exact log and a coordinate-normalization suggestion. This is the immediate upstream blocker; fix it, then rerun the complete manual-only `.github/workflows/agent48-champion-root.yml` and inspect the new endpoint theorem axiom output. Do not restore automatic push/PR triggers merely to obtain a run.

No claim should be promoted to `results/` unless the source-closure compilation succeeds and the theorem dependencies contain no `sorryAx`.

The finite q4 screens remain in [LCIncQ4Cut.md](LCIncQ4Cut.md) as empirical evidence only. Neither the q4 prefix nor this uncompiled composition determines BB(6) or supplies a universal six-state upper bound.
