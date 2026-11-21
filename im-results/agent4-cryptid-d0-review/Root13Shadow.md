# Thirteen-step 3-adic raw-replay shadow of the authentic root

**Status:** exact BigInt computation using the repository's DRegular model and the sparse raw-machine A_step2 replay simulator. This is not yet a Lean proof of the full original-machine path.

## Root section and modular certificate

Let

`C = 1975700577069254261393123959451562008800234946348086`

be the empty-suffix parameter at the start of the external halting-cylinder path.

In the authentic-root arithmetic chain from `L(9,0,0)`, section index **31,777** has state `L(a,0,0)` and satisfies:

- `a - C ≡ 3^13 (mod 3^14)`;
- writing `a = C + 3^13*p`, we have `p mod 2187 = 205` (so `p mod 81 = 43` and `p mod 3 = 1`);
- `a mod 3^20 = 2863782241`;
- `a` has 44,970 bits.

The congruence is exact to 14 powers of three: the difference is divisible by 3^13 but not 3^14. This is deeper than the previously reported seven-step shadow at index 2,640.

## Thirteen-macro replay

The first ten transitions are the exact DRegular path. The `Root13Section.lean` draft connects the root section to the external start by the existing `DRegularShift.run_shift` theorem.

Transition 11 is also covered by the existing `BlankSixthExceptional.first_nonregular_original` theorem, which invokes `BB6.Agent32EAll.all_e_double_implicit_blank` with q=3 and the root's lifted parameter `k_root=3*t6+1`. Its output suffix is exactly `0 1^8 0 1^6`.

Crucially, I then replayed transitions 11–13 on the lifted root parameter using the same sparse raw-machine `replay_macro` implementation that generated the external trace. The root's internal sweep parameter K is enormous and differs from the external K, but the same A_step2 arguments (35, 21, 5) apply. The replay confirms the same branches and exact output suffixes, and the expected 3-adic valuation drop.

| Macro | Branch | A_step2 argument | Input residue | v3(output parameter difference) | Output suffix |
|---:|:---:|---:|---:|---:|---|
| 1 | E | 13 | 1 | 12 | `0111111` |
| 2 | E | 21 | 1 | 11 | `01010111` |
| 3 | B | 5 | 2 | 10 | `010111` |
| 4 | B | 5 | 2 | 9 | `0111` |
| 5 | E | 21 | 1 | 8 | `01010` |
| 6 | B | 5 | 2 | 7 | `010` |
| 7 | E | 17 | 1 | 6 | `011111111` |
| 8 | E | 21 | 1 | 5 | `0101011111` |
| 9 | B | 5 | 2 | 4 | `01011111` |
| 10 | E | 27 | 1 | 3 | `010101011` |
| 11 | E | 35 | 1 | 2 | `0111111110111111` |
| 12 | E | 21 | 1 | 1 | `01010111110111111` |
| 13 | B | 5 | 2 | 0 | `010111110111111` |

After i matching updates, the parameter difference is

`a_i - n_i = 8^i * 3^(13-i) * p`.

The raw replay verifies the update sequence through macro 13. Since p is not divisible by 3, after macro 13 the root's next input has residue 1, whereas external macro 14 has residue 2. The paths therefore diverge at macro 14.

## Source-proof status and limitations

- The root index is the section/return index used by `check_root17.py`, not a primitive-step count.
- The arithmetic chain uses `check_eighth_root.py`'s exact integer DRegular transition and exceptional-reentry functions.
- `Root13Section.lean` extracts the 4,484-step prefix from `Agent25SixthRoot.seed`, ten DRegular transitions before the sixth exceptional endpoint. It attempts to prove the exact shape and modular certificate, the first-ten affine lift, and source reachability using `Agent25RootChain.extend_regular`. This file is **uncompiled**.
- Transition 11 is covered by `BlankSixthExceptional.first_nonregular_original` and `Agent32EAll.all_e_double_implicit_blank`.
- Transitions 11–13 are independently replayed by the sparse raw-machine simulator, but this replay is not a kernel-checked proof. The remaining formal task is to certify these raw macro replays (including the lifted K values) in Lean and compose the raw-machine/CryptidBoundary conjugacy.
- A scan through the episode-20 arithmetic lookahead found no exact hit of the external cylinder `a ≡ C (mod 3^108)`. Among DRegular states with `q=b=0`, the maximum observed `v3(a-C)` was 13, uniquely at index 31,777. This finite scan covers DRegular states and explicit reentry endpoints, not every primitive configuration inside exceptional packets.
- This does not establish halting or the exact value of BB(6).

## Reproduction

- `python3 root13_shadow_check.py`: root congruence and first-ten affine lift.
- `python3 root13_raw_macro_shadow.py`: raw replay of macros 11–13 on the lifted root parameter.
- `node root20_cylinder_screen.mjs`: broader DRegular-state screen through the episode-20 arithmetic lookahead.

The raw replay script imports `replay_macro` from `cryptid_A_step2_replay.py`, the same sparse simulator used to generate `macro_trace.json`.


## Post-divergence reconvergence to the sixth q4 rejoin

After macro 13, the root residue is 1 while external macro 14 has residue 2. Replaying the root-specific raw prefix lengths by searching for the first valid A_step2 sweep precondition gives:

- macro 14: branch E, shortest valid prefix m=23, output suffix `0101010110111111`;
- macro 15: branch A, shortest valid prefix m=26, output suffix `01010111`.

The output suffix `01010111` is the DRegular `(q,b)=(3,2)` suffix. More strongly, its unary parameter is **exactly equal** to the existing sixth q4 rejoin target
`32768*s6 + 28577`, where `s6=(t6-23)/27). This is the target of `BlankSixthQ4Rejoin.sixth_q4_root_rejoin_original`.

The updated `root13_raw_macro_shadow.py` reproduces this equality, including the bounded first-valid-prefix search for m=23 and m=26. Thus the root-specific detour after divergence at macro 14 reconnects exactly to the already source-certified sixth q4 DRegular reentry state. This is computational raw-replay evidence; the formal source composition remains to be written.
