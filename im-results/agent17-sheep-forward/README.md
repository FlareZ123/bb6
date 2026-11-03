# A complete 3-adic abstract transition graph for Sheep's first-even return

**Status (2026-11-03): intermediate method-limit result, rigorous elementary proof with a Lean-kernel-certified lifting lemma and an independent exact integer checker.** This establishes no reachability of synthetic starting states from the blank tape, does not decide the Sheep machine, and does not change any BB(6) bound. It is therefore in `im-results/`, outside `results/`. Programme: [R010](../../research/issues/R010.md).

## Original machine and exact scope

The six-state Sheep table is `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`. The authentic blank-return entry is `5`, followed by `5→7→10`. For `t=2^a u≥5` with odd `u`, the nonterminal return formula is

- `F(t)=t+a+3` for `u=3`;
- `F(t)=t+a+(u−1)/2` for `u≥5`;
- `u=1` is terminal.

Agent16's source-linked even-return theorem `BB6.Agent16.SheepEvenSource.raw_halts_iff_even_power` reduces the real halting question to whether the first-even-return orbit from 10 visits some `2^j`, `j≥2`. For a nonterminal input `t`, let `F(t)−1=2^h w` with `w` odd. Then its exact first even return is `E(t)=1+3^h w`. In particular, if `F(t)` is already even, `E(t)=F(t)`. This reduction was certified against the original Google DeepMind machine in [manual CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547); its earlier source and derivation are in [Agent16's dossier](../agent16-sheep-even-return/README.md).

## Theorem: every pair of 3-adic residue classes has a genuine edge

For **every** integer `k≥1`, set `q=3^k`. For every pair of residues `0≤r,s<q` and every bound `N`, there are integers `b≥1`, odd `u≥5`, and `x=4^b u≥N` such that:

1. `x` is even and is a genuinely nonterminal Sheep-section input.
2. `F(x)` is even, so the first-even successor is exactly `E(x)=F(x)`.
3. `x≡r (mod q)` and `E(x)≡s (mod q)`.

In fact we can require `u≡1 (mod 4)`, so only the already-published generic branch is needed. These transitions occur between authentic **individual legal section states**, although their *source states have not been shown reachable from the blank entry*. The associated directed quotient graph on residues modulo `3^k` is therefore a complete digraph including loops.

### Lemma: exact modular surjectivity

Define `P(r,c,b)=4^b(4b+c)+r` for natural `r,c,b`. For every natural `r,c,k`, there exists `0≤b<3^k` with

`P(r,c,b)≡0 (mod 3^k)`.

**Proof.** The elementary cubic lifting identity, independently kernel-checked in [Agent39's source](../agent39-sheep-zero-ancestry/ThreeAdicOrder.lean), yields

`4^(3^j)=1+3^(j+1)Q_j`

for a natural integer `Q_j`. Also `4^b=1+3W_b` for some natural `W_b`. Direct expansion therefore gives the exact congruence

`P(r,c,b+3^j)≡P(r,c,b)+3^j (mod 3^(j+1))`.

At `j=0`, the residue `P(r,c,0)=c+r` is arbitrary modulo 1, with `b=0`. If a root `b<3^j` is known modulo `3^j`, its residue modulo `3^(j+1)` is one of `0, 3^j, 2·3^j`. Shifting `b` by respectively `0, 2·3^j, 3^j` yields a root at the next level. The new `b` remains below `3^(j+1)`. Induction establishes the lemma. The **complete Lean 4.36.0-rc2 proof** is in `ForwardSurj.lean`, including theorem `p_root_lt` and axiom audit `[propext, Classical.choice, Quot.sound]`. `Three.lean` contains the recompiled, attributed cubic-lifting proof.

### Complete edge construction

Fix `q=3^k`, `r,s<q`. Put

`c=2r+2q−2s−1`,

which is a positive natural number because `s<q`. The lemma supplies `0≤b<q` with `P(r,c,b)≡0 (mod q)`. The same cubic-lifting identity gives `4^q≡1 (mod q)`, so choose `B=b+q≥1` and note

`P(r,c,B)≡0 (mod q)`.

Choose any `u≥5` satisfying simultaneously

`u≡r·4^(q−b) (mod q)`, and `u≡1 (mod 4)`.

These congruences have arbitrarily large solutions by the elementary Chinese remainder theorem since `q` is odd. Set `x=4^B u`. Then `v₂(x)=2B`, the generic branch applies, and

`E(x)=F(x)=x+2B+(u−1)/2`,

which is even because `u≡1 (mod 4)`. Since `4^q≡1 (mod q)`,

`x≡4^(b+q)·r·4^(q−b)≡r (mod q)`.

Multiplying the identity `P(r,c,b)≡0` by `4^(q−b)` and simplifying `4^q≡1` yields

`4b+c+u≡0 (mod q)`.

Finally,

`2E(x)≡2r+4B+u−1≡2r+4b−(4b+c)−1≡2s (mod q)`.

As `q` is odd, `E(x)≡s (mod q)`. Increasing `u` by arbitrarily large multiples of `4q` preserves every condition and makes `x≥N`. QED.

### Consequence: no residue-only forward invariant at any fixed 3-adic resolution

Let `A⊆{0,…,q−1}` describe a predicate `I(x) :⇔ x mod q∈A` **on all even section inputs**. Assume `10 modq∈A` and `I` is preserved under every genuine nonterminal first-even transition, for inputs beyond any fixed finite threshold. By the theorem, for any `r∈A` and any residue `s` an eligible even input `x` with `x modq=r` and `E(x) modq=s` exists. Closure forces `s∈A`, so `A` is the entire residue set. Such a predicate cannot exclude any halting power `2^j`.

The conclusion concerns a **globally inductive full-residue-class predicate**. It does not rule out invariants incorporating higher 2-adic structure, unbounded history, special subsequences, or an actual blank-orbit restriction. It also does not imply the real Sheep orbit visits every residue. More refined mechanisms remain possible.

## Verification and reproduction

- `Three.lean` and `ForwardSurj.lean`: locally compiled with Lean **4.36.0-rc2**, no `sorry`/`admit`/`native_decide`, theorem `p_root_lt` uses only standard logical axioms. These are *self-contained local mathematical statements*, not a newly checked original-machine import. The original-machine even-return bridge is independently certified in the cited CI.
- `construct.py`: standalone Python 3 exact constructor. It independently computes modular inverse powers and the CRT odd part, then directly evaluates the published `F` and checks that its output is even. Tested **all 7,380 pairs** for `q=3,9,27,81` and **4,000 deterministically sampled pairs** for `q=243,729,2187,6561`: **11,380/11,380 passed** with seed `20261103`.
- Example with `q=2187`, `r=10`, `s=2`: `b=434`, `u=6997`, `x=4^434·6997` has source bit length 881, and its genuine even successor has target residue `2`. The printed `b` refers to the directly constructed witness and need not be shifted by `q` as in the uniform proof.
- A separate finite direct orbit probe observed all residues mod `3,9,27,81,243` among the first 100,000 even returns from 10; this observation supplies no all-time reachability theorem.

**Research implication:** For Sheep, increasing a finite 3-adic modulus while retaining only the current even state cannot provide a global induction barrier. A more powerful candidate would need to encode correlations with the 2-adic block length, a constrained forward language of reachable words, or another orbit-dependent feature. The primary halting question remains unresolved.

## Sources and novelty limits

- [Original published Cryptids BB6 research](https://github.com/google-deepmind/cryptids/tree/main/BusyBeaver/BB6) and the original-source bridge in `im-results/agent22-sheep-semantic-bridge/`.
- [Agent16, full even-return reduction](../agent16-sheep-even-return/README.md), source CI 41505950547.
- [Agent39, 3-adic zero-valuation ancestry](../agent39-sheep-zero-ancestry/README.md), whose power-lifting lemma is reused with attribution.
- [Agent17 previous symbolic inverse method](../agent17-sheep-third-generation/SYMBOLIC-SIEVE.md) and [arbitrary-modulus inverse corridors](../agent17-sheep-arbitrary-modulus/README.md). These concerns about deep *backward* trees differ mathematically from the present *forward* quotient-completeness argument.

The quotient-completeness result has not had independent peer review or exhaustive external-prior-art assessment. It is a narrow, reproducible methodology result and is **not presented as an externally novel publication claim**.

## Follow-up: complete quotient graph for **every odd modulus**

The preceding `3^k` theorem has now been generalized in the independent [all-odd-modulus proof](ALL-ODD-MODULI.md). For any odd `m>1` and any residue pair `r,s mod m`, there are arbitrarily large genuine generic first-even transitions from residue r to residue s. The proof adds prime powers in ascending order, using a nondegenerate order-of-4 lifting step to solve `4^b(4b+c)+r≡0 (mod m)`. Its standalone [exact implementation](general_odd.py) passed 11,500 structured tests including composite moduli. This **larger general theorem currently has a full written proof and exact tests, but its prime-by-prime lifting has not been certified in Lean**. The narrower power-of-three lemma remains independently kernel checked in the two Lean source files. Both conclusions concern legal *synthetic* source states; no blank-orbit decision follows. See the linked report for quantifiers, proof, limitations, and precise dependencies.

## Mixed-modulus consequences and authentic finite-prefix witness

The [zero 2-adic fiber theorem](ZERO-FIBER.md) strengthens the all-odd construction: for `m=2^k n`, `n` odd, every source residue divisible by `2^k` has genuine synthetic first-even transitions to **every even target residue modulo m**. The new written proof uses the same ascending-prime root lifting with the additional constraint `2^(k−1)|b`. It is checked by [6,240 exact constructed cases](zero_fiber.py), but this broader prime-by-prime lemma is not yet Lean formalized.

A separate [exact authentic prefix certificate](blank_prefix.py) reconstructs **65,924 first-even returns from genuine entry 10**, checking each compressed jump against direct iteration of the raw published `F`. The endpoint has `v2=17`, 52,736 bits, and recorded SHA-256. Thus [FINITE-MODULI-17.md](FINITE-MODULI-17.md) proves an additional method-limit theorem: for **every** finite modulus `m` with `v2(m)≤17`, no proper subset of its even residue classes containing the genuine initial residue can be globally inductive under every legal first-even return. The finite prefix is computationally cross-checked; it is not a separately Lean-certified 65,924-step trace. The universal zero-fiber component has a conventional proof pending independent peer audit. Neither result makes an unbounded valuation claim or a BB(6) decision.

## November 3, 21:17 UTC: all-3-power edges certified in Lean

The earlier paper-plus-exact-constructor all-`3^k` theorem now has an **end-to-end local Lean 4.36.0-rc2 kernel proof** reusing the unchanged existing `Three.lean` and `ForwardSurj.lean`. New committed files:

- [`ForwardEdgeAlgebra.lean`](ForwardEdgeAlgebra.lean): `generic_edge_from_root` and `generic_edge_from_root_unbounded` convert a checked polynomial root into a legal even generic section edge. Its exact equation is `x=4^b*u=2^(2*b)*u`, `u>=5` odd, `y=x+2*b+(u-1)/2`. The witness `x` can exceed any prescribed `N`. These statements work for any odd modulus `q=2t+1` provided the root exists.
- [`ForwardThreeEdge.lean`](ForwardThreeEdge.lean): `positive_root_three` uses the previously proved `p_root_lt` and modular shift to obtain a **positive** root for every `3^k`. The final `three_power_all_edges` proves, for every `k,r,s,N : Nat` with `r,s<3^k`, existence of `b>=1, u>=5` odd, even `x,y`, `x>=N`, the exact generic Sheep section-return equation, and `x%3^k=r`, `y%3^k=s`.

**Observed local verification:** reconstructed `Three.lean` and `ForwardSurj.lean` verbatim from their already committed source, compiled them into `.olean` modules, compiled both new files against those actual modules, and evaluated `#print axioms`. Final `BB6.Agent17Forward.three_power_all_edges` printed `[propext, Classical.choice, Quot.sound]`; both other new final theorems printed the same ordinary axiom set. There is no `sorry`, `admit`, `native_decide`, unproved postulate or mathematical oracle. Compiler: local Lean 4.36.0-rc2. New source hashes (SHA256 of UTF-8 bytes): `ForwardEdgeAlgebra.lean` = `3778fc00fa5d82360e4b17dda58fb351e1582c4a14ae0b91dc2022063ae52944`; `ForwardThreeEdge.lean` = `fc76279f2d4c06c3b2c8cf40ec3d9329d9a9b097f9b709468a26b00febcc40b2`. Reproduce by compiling `Three.lean`, then `ForwardSurj.lean`, then `ForwardEdgeAlgebra.lean`, then `ForwardThreeEdge.lean` in one Lean search path.

**Exact evidence boundary:** This upgrades the earlier *same mathematical 3-adic synthetic quotient theorem* from a written proof to an end-to-end standard-axiom Lean proof. It is a mathematical provenance advance, with no claim of previously unknown mathematical content or of external academic novelty. The final theorem proves legal individual generic section transitions in the **published Sheep return formula**. It does not import the pinned original six-state machine in the two new files; Agent16's separate upstream source-to-section bridge is already certified in CI 41505950547. Synthetic source states are free to depend on `r,s,N`. No conclusion about true blank-origin reachability from 10 or a BB(6) bound follows.

Next decisive question: a genuine **seed-sensitive** language/valuation-history obstruction, or a source-composed Lean theorem that does not lose the quantifier distinction between independently chosen synthetic states and the single true orbit.
