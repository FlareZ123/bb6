# S4 third nested source-G section: 28,802 gates per 214,748,364,800,000 reduced returns

This is a **third, exact all-suffix partial-return reduction conditional on computed prefix-section premises**, extending the previously derived [386-gate](SUFFIX-RENORMALIZATION.md) and [4,603-gate](NESTED-SUFFIX-RENORMALIZATION.md) word maps. The universal stage/word decomposition is proved in [S4SuffixBoundary.lean](S4SuffixBoundary.lean) and [S4BoundaryWord.lean](S4BoundaryWord.lean) without `sorry`, and was compiled locally against exact copies of the original source `H/G` definitions. All three *large numeric period assertions* remain native exact-integer computations, pending separate Lean-kernel certificates. S4/BB(6) remain open.

## Third-level reduction

Let `P=G509;G290;G219`, `T=20971520`, and `Q` the 386-gate first-level effective partial suffix map, acting after the computed 18-prefix section `p*`. Let `R` be the 4,603-gate second-level effective partial map, acting after the computed ten-digit section `r*`, which repeats every 12,800 `Q` blocks.

One successful `R` operation on the modeled rooted eight-digit tail yields a stack of length 15. Its first seven digits are:
```text
s* = [146121173630, 123211293236, 150769158159,
      655928122993, 1188500987335, 5911406347889, 4869186526586]
```
The exact finite-source-prefix projection of the `R` word satisfies `prefixWord_R^800(s*)=s*`. The source-shaped genuine-root model reaches this section at accelerated return **270,680,724,817**, conditional on its as-yet-unformalized finite bridge after the original Lean-certified 5,457-return root. The period is witnessed; it is not claimed globally minimal.

Every original `G` operator in the chronological `800*4603=3682400` stage word either leaves the tail beyond seven digits untouched, adds a positive amount to its first digit, or acts there by an actual partial `G` gate. The exact computed boundary inventory is:

| Item | Exact value |
| --- | ---: |
| Second-level `R` operations per third block | 800 |
| Original reduced `P` returns per third block | 214,748,364,800,000 |
| Source `G` operations in the uncompressed `R` word | 3,682,400 |
| Boundary head additions | 28,830 |
| Boundary partial `G` gates | 28,802 |
| Trailing head addition after gate normalization | 0 |
| Sum of normalized positive `G` offsets | 219,902,325,555,142,396 |
| Sum of `offset+2`, exact successful mass gain | 219,902,325,555,200,000 |

All values are exact unsigned-integer arithmetic, with no floating-point approximations. The mass identity is `219902325555142396 + 2*28802 = 1024*214748364800000`.

Let `V` denote the 28,802-operation normalized partial `G` word. The source operator factorization gives the **all finite suffixes, all halting cases** mathematical identity
```text
R^800(s* ++ S) = Option.map (s* ++) (V S).
```
Composing with both earlier fixed sections gives
```text
P^214748364800000(p* ++ r* ++ s* ++ S)
  = Option.map (p* ++ r* ++ s* ++) (V S).
```
These identities require the finite computed prefix cycles and their source-compatible `G` projection; their operator semantics are exact and do not suppose an infinite surviving root.

## Fully reproducible finite computational check

The standalone C++20 program [s4_third_macro.cpp](s4_third_macro.cpp) imports the common exact source-G implementation from [s4_suffix_macro.cpp](s4_suffix_macro.cpp) and parses the `Offsets:` and `RootTail:` lines emitted by [s4_nested_macro.cpp](s4_nested_macro.cpp) in its optional `--print-offsets` mode. Compile the two programs in the same directory with C++20 assertions enabled, then stream the second-level program's output to the third-level executable. No pre-generated 4,603-number dataset is necessary. The third-level executable reproduces the 800-period equality, 28,830/28,802 boundary count, offset sum, and successful mass identity. It independently evaluates the original 3,682,400-step full second-level `G` word from the model root and the compressed 28,802-step third-level word on its eight-digit suffix; the **complete resulting stacks agree**.

This third level makes further genuine-tail forward/inverse study inexpensive at approximately 215 trillion original reduced returns per effective return. The still-open mathematical task is a **root-history all-time invariant or an actual halting witness**, with numerical source-cycle proof obligations handled separately. Successive finite-depth periodic sections alone do not imply S4 nonhalting.
