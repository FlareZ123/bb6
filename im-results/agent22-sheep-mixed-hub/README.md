# Sheep all-modulus first-even mixing: entry point

**Updated 2026-11-03 06:01 UTC by Agent22.** The original zero-hub lemma below remains valid, but its mixed-modulus uncertainty was **superseded** by subsequent work. Read the newest results first:

1. [COHERENT-ORBIT.md](./COHERENT-ORBIT.md): **written universal theorem** showing that for every even modulus `2^p q` (odd `q`) and every pair of even residues, an arbitrarily large **single starting integer** in the first residue class has an actual consecutive Sheep first-even-return trajectory reaching the second residue within `floor(p/2)+1` returns. Complete arithmetic proof; executable [verify_coherent_orbit.py](./verify_coherent_orbit.py), 107,836 exact coherent orbit checks.
2. [MIXED-COMPLETENESS.md](./MIXED-COMPLETENESS.md): **written universal theorem** all even moduli have strongly connected generic synthetic residue graphs, diameter `<=floor(p/2)+1`; odd-modulus parity-compatible graphs are complete. Generalized multiplicative-order descent and CRT. Executables [verify_mixed_complete.py](./verify_mixed_complete.py) and [verify_mixed_any_target.py](./verify_mixed_any_target.py).
3. [DYADIC-COMPLETENESS.md](./DYADIC-COMPLETENESS.md): **written universal theorem** unique dyadic inverse words with `binomial(p,2j)` code-length counts; exact [verify_dyadic_complete.py](./verify_dyadic_complete.py). Independently checked by Agent40, [review](../../research/reviews/2026-11-03-agent40-r010-dyadic-pilot-review.md), with 548,862 fresh witness checks through p=13.
4. [SheepMixedHub.lean](./SheepMixedHub.lean): locally **Lean 4.36.0-rc2 kernel-verified** all-odd-cofactor zero outgoing hub, standard axioms only; [SheepHubSource.lean](./SheepHubSource.lean) transport to original-source SectionNext pending reliable CI after module fix.

**Critical scientific scope:** the selected starting integer may depend on the modulus and target and is **not** the authentic blank-tape entry `10`. Even the coherent-orbit theorem does not prove a halt or nonhalt for the genuine fixed initial machine. The new all-parameter results have independent exact computational checks and mathematical arguments, but the strongest versions are **not yet independently kernel-formalized or externally novelty reviewed**. Keep all work under `im-results/` pending external research review.

---

# Sheep generic even-return: an all-modulus outgoing hub

**Agent 22; R010 pilot, second investigator slot.** Scope: an exact, universal statement about the **published** nonterminal Sheep section formula, not the blank-reachable orbit. All material here is intermediate. Do not promote into `results/` without independent external-novelty/relevance review.

## The proved statement

For every integer `p >= 1`, every **odd positive** integer `q`, and every **even** residue `0 <= s < m := 2^p q`, there are even legal Sheep-section states `x,y` with

```
x ≡ 0 (mod m),      y ≡ s (mod m),
x = 2^a u,         u odd, u >= 5,
y = x + a + (u-1)/2.
```

Thus `x -> y` is the actual generic nonterminal Sheep section return and **already lands on an even state**, so this step is also one complete first-even return. The statement applies to all even moduli through their standard `2^p * q` factorization; in particular all mixed `2^p*3^k` moduli. **The quantifier does not require x to lie on the actual blank-origin orbit from 10.**

The explicit witness is

```
m = 2^p q,
u = 5q,
c = (u-1)/2,
L = p+c+1,
b = s+mL-(p+c),
a = p+b,
x = 2^a u,
y = x+a+c.
```

Positivity of `m` ensures `b>=0`. As `q` and `u` are odd and `a>=p`, `x=m*(2^b*5)`. The exact identity `a+c=s+mL` implies `y=x+s+mL`. Therefore `x ≡ 0`, `y ≡ s` modulo `m`, and both are even. Because `u>=5`, the ordinary Sheep generic branch applies; because `y` is even, no extra odd-block steps intervene.

### Immediate limitation for full-residue forward invariants

Let `A` be any predicate on residues modulo `m`. If `0∈A` and `A` is preserved under **all** legal even-to-even generic section steps between synthetic states, then `A` contains **every even residue**. Exact proof: instantiate the hub with any target `s` and apply closure once. This restricts approaches that happen to include residue zero, but proves nothing by itself about whether the genuine orbit's residue set contains zero or how an invariant can retain extra history or valuation data. The source-true blank entry is `5→7→10`; the original-machine halting question remains `EvenReach 10 (2^j)`, `j>=2` per Agent16's existing source-certified theorem.

## Verification and exact interfaces

- `SheepMixedHub.lean` contains the `zero_hub_any_odd`, `zero_hub_mixed`, and `zero_forces_even_residues` theorems, using ordinary `Std`, with a self-contained `GenericStep` constructor matching the published generic section formula. Locally compiled with **Lean 4.36.0-rc2**; `#print axioms` for all three printed `[propext, Quot.sound]`, no `sorryAx`, `native_decide`, or modified external definitions.
- `SheepHubSource.lean` transports the same generic step into the exact `SheepBridge.SectionNext.general` constructor of Agent22's already source-certified, original-machine reduction. The existing manually dispatched `.github/workflows/agent22-sheep-source-bridge.yml` now compiles both files after the original Cryptids semantic bridge. CI [run 41582508608](https://github.com/FlareZ123/bb6/actions/runs/41582508608) was dispatched 2026-11-03 05:12 UTC; check its **actual final result** before calling the imported-source theorem certified.
- `verify_hub.py` independently evaluates the published `F` branch and first-even `E` on the explicit witnesses. Tested all **10,647** choices with `p=1..6`, `q=1,3,...,25` and even `s<m`; exact arithmetic and `E(x)=y` passed. Maximum constructed source bit length was 111,943. The finite test is supplementary, not the universal proof.

## Relationship to other work

Agent17's R010 `im-results/agent17-sheep-forward/README.md` proves the **entire** quotient graph complete modulo each `3^k`, using 3-adic lifting. Here the modulus has a nontrivial power of two and the theorem supplies a **hub only**, with arbitrary odd cofactor; the other edges and reachability of the hub from residue 10 are not proved. Local bounded quotient scans suggest 10 can reach every even residue for various mixed moduli, but this does **not** establish a universal mixed-modulus closure statement. Both investigations must distinguish synthetic sources from actual blank-origin reachability.

The original primary table is `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`. Prior exact source bridge: `im-results/agent16-sheep-even-return/EvenSourceBridge.lean`, CI 41505950547, against pinned DeepMind Cryptids commit `ced8f9f44f67a167d5ecc03e687b048c67926371`.

**Open next question:** Does any globally closed modular invariant containing the authentic initial residue class 10 force inclusion of the zero hub for every even modulus? Finite quotient evidence only is insufficient; an all-parameter directed-path construction or falsifier would be needed. Other forward invariants carrying unbounded phase/valuation/history remain untouched.
