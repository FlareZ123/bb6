# Thirteen-step 3-adic raw-replay shadow of the authentic root

**Status:** exact DRegular arithmetic plus kernel-checked original-source Lean proof of the root segment from section 31,777 through the sixth exception and next regular reentry. The episode-20 cylinder screen remains finite evidence; this is not a halting/nonhalting verdict.

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

The output suffix `01010111` is the DRegular `(q,b)=(3,2)` suffix. Its unary parameter is **exactly** `32768*s6 + 28577`, where `s6=(t6-23)/27`.

This is the same endpoint independently certified by Agent 36's original-source theorem `BB6.Agent36SixthBlank.blank_sixth_reentry`, which composes `BlankSixthExceptional.sixthException_original` with `BB6.Agent36SixthPacket.five_return`. In that proof, `v=t6/27` and the checked residue `t6 mod 27 = 23` gives `v=(t6-23)/27=s6`. The original-source checks are CI runs [41753103349](https://github.com/FlareZ123/bb6/actions/runs/41753103349) (`five_return`) and [42139587484](https://github.com/FlareZ123/bb6/actions/runs/42139587484) (`blank_sixth_reentry`). Do **not** cite `BlankSixthQ4Rejoin.sixth_q4_root_rejoin_original` as proof: its targeted audit was cancelled, and Agent 37 explicitly identified it as an unverified alternative to the accepted Agent 36 route.

The raw replay's macro-14/15 decomposition and first-valid-prefix search remain simulator evidence. The physical endpoint from the sixth q4 input is nevertheless source-certified by Agent 36's existing theorem; no new A_step2 formalization is needed merely to certify that endpoint.

Although this endpoint has the same `(q,b)=(3,2)` suffix as external prefix j=2, it is **not** a return to that external halting cylinder. At the root's later reentry section index 31,792, its parameter is 0 modulo 3, while the external macro-2 base parameter `C_2=14049426325825808081017770378322218729246115174030817` is 2 modulo 3; hence `v3(a-C_2)=0`. The rejoin is to the source-certified Agent 36 regular state, not to the external 107-call branch.


## Comparison with all canonical states on the external halting path

The external 107-call trace has canonical A-section states only at prefix indices j=0,...,10. Write the state after j macros as `A(C_j + 3^(108-j)*8^j*k, r_j)`, where `C_j` is its k=0 unary parameter and `r_j=(01)^q 1^b` is the suffix. The new `root20_suffix_cylinder_screen.mjs` compares every modeled authentic-root DRegular section with every such state having the same canonical suffix.

For each j, the unique maximum of `v_3(a-C_j)` occurs at authentic-root section index `31777+j`, with value `13-j`:

| External prefix j | Root section index | Suffix (q,b) | Maximum v3(a-C_j) |
|---:|---:|---:|---:|
| 0 | 31777 | (0,0) | 13 |
| 1 | 31778 | (1,5) | 12 |
| 2 | 31779 | (3,2) | 11 |
| 3 | 31780 | (2,2) | 10 |
| 4 | 31781 | (1,2) | 9 |
| 5 | 31782 | (2,0) | 8 |
| 6 | 31783 | (1,0) | 7 |
| 7 | 31784 | (1,7) | 6 |
| 8 | 31785 | (3,4) | 5 |
| 9 | 31786 | (2,4) | 4 |
| 10 | 31787 | (4,1) | 3 |

The script found **no exact lift** `a=C_j+3^(108-j)*8^j*k` with `k≥0` among the 82,605 modeled sections/reentry endpoints through episode 20. This recovers the 13-step near-shadow as a single coherent descending valuation profile, rather than only a comparison of the first 13 raw macros. It remains a finite arithmetic-model result.

## Additional suffix-cylinder screen

The same run checked the extended candidate halting suffixes from Agent 32's final-tail work. The base is `C mod 3^10 = 23839`.

| Suffix (q,b) | Modeled sections | Maximum v3(a-C) | Hits modulo 3^10 |
|---:|---:|---:|---:|
| (1,0) | 201 | 5 | 0 |
| (1,1) | 0 | — | 0 |
| (3,1) | 1 | 0 | 0 |
| (4,1) | 5 | 3 | 0 |

Thus none of those four classes reaches even the necessary modulus `a ≡ C (mod 3^10)` in this finite screen. For comparison, `(4,0)` has one weaker-modulus hit at section index 27,282 and maximum valuation 11, but it is not among the currently established final-tail classes; `(3,2)` has maximum valuation 8 relative to C. These checks cover only DRegular sections and explicit reentry endpoints represented by the script, not every primitive configuration inside exceptional packets, and prove no all-time exclusion.
