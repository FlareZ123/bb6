# Fixed-modulus forward-invariant obstruction through 17 powers of two

**Status:** Intermediate mathematical consequence of a reproducible finite authentic Sheep section prefix and the written zero-fiber theorem. The 65,924-step finite prefix is exact-integer Python checked through two independent transition calculations, rather than kernel formalized. There is no new BB(6) bound or resolved holdout. Programme R010.

## Uniform theorem

For any positive modulus `m` whose 2-adic valuation is at most 17, let `A` be a subset of the **even** residue classes modulo `m`. Define `I(x)` on legal even Sheep section inputs by `x mod m in A`. If `I(10)` holds and `I` is closed under every genuine nonterminal first-even return, then `A` contains **all even residues**.

This rules out a globally inductive proof that relies exclusively on one fixed residue modulo any such modulus. Other types of invariants, including restrictions tied to actual blank-reachable states, may still succeed.

## Proof

If `m` is odd, use [the complete all-odd quotient graph theorem](ALL-ODD-MODULI.md): from any included residue there exists a legal first-even transition to every other residue. Thus `A` is full.

If `m=2^k n` with `1<=k<=17` and `n` odd, follow the authentic blank-section even orbit from 10 for exactly 65,924 first-even returns. The independently verified final state `t_65924` has `v2(t_65924)=17`. Closure of `I` forces its residue into `A`, since every preceding edge is genuine. Therefore `A` includes a residue divisible by `2^k`. [The zero-fiber theorem](ZERO-FIBER.md) constructs, for each even target residue modulo `m`, a genuine one-step first-even return from **some** legal even source in that included residue class. Closure forces all such targets into `A`. This argument depends critically on full-residue-class induction rather than any claim that the synthetic alternative sources are blank-reachable. QED.

## Reproducible finite witness

[`blank_prefix.py`](blank_prefix.py) reconstructs the literal Sheep return trajectory from section entry 10. At every macro step it independently compares an iterative sequence of exact raw F calls to the even-accelerated closed formula, checking equality of both target and raw-step count. It verifies strict increase and nonterminal legality through the entire prefix.

The 65,924th even state has:
- 2-adic valuation **17**;
- bit length **52,736**;
- residue **269057283** modulo **1000000007**;
- SHA-256 of minimal big-endian unsigned integer bytes:
  `3313b753edcd2584a561fee50f67b1aa7db7f58be804c67600205aa9867e6b37`.

The initial attainment indices for new valuations were:
`(0,1),(1,2),(4,3),(7,4),(17,5),(21,6),(198,8),(506,9),(1603,10),(2144,11),(2456,13),(3376,14),(6909,16),(65924,17)`.

All 65,924 edge comparisons passed in a local Python 3 standard-library run. Original machine-to-section/even-return semantics are separately Lean source-certified by Agent16's [CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547). The finite prefix here is exact-computational evidence rather than a Lean certificate.

## Future direction and limitations

If one could prove that the **actual blank-origin first-even orbit has unbounded 2-adic valuations**, this argument would extend to every positive finite modulus. Such a claim is currently entirely open. The finite observed valuation 17 cannot imply unboundedness.

The all-odd and zero-fiber arithmetic theorems have complete conventional written arguments and exact checkers, but their general prime-factor induction awaits independent audit and full Lean formalization. The root `3^k` lifting lemma is separately kernel checked. None of the present conclusions proves halting or nonhalting of the Sheep Machine, and none determines BB(6).

## Independent pure-power-of-two Lean certificate

[PureTwo.lean](PureTwo.lean) locally compiled in Lean 4.36.0-rc2 and proves the all-k zero-fiber reachability theorem for moduli `2^k` by explicit construction, with only `[propext, Quot.sound]` axioms. The arbitrary odd-factor part of the uniform theorem uses the separate conventional CRT / prime-digit proof; its absence of a Lean file must not be concealed.
