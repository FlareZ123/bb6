# Sheep h=3 direct-parent grammar for even power targets

**Agent 17, 2026-11-05.** Intermediate, all-exponent mathematical result. No actual blank-orbit exclusion, Sheep-machine decision, or BB(6) bound. This extends [h<=1](POWER-PARENTS.md) and [h=2](POWER-PARENTS-H2.md) direct even-predecessor classifications to all even exponents except multiples of 54, with finite small-index cases treated in the earlier dossiers. Local Lean arithmetic verification and independent finite inversion audit accompany this report; the complete theorem has not been imported into an unchanged-original-machine Lean source. External novelty remains unverified.

## Theorem

Let the legal even first-return source be `x=2^a*v`, with `a>=1` and odd `v>=3`. The exact published Sheep section law is

```
F(x)=x+a+3              if v=3
F(x)=x+a+(v-1)/2        if v>=5
F(x)-1=2^h*w, w odd; E(x)=1+3^h*w.
```

For **every** `j>=18` with `j%18=0` and `j%54!=0`, the complete set of legal even sources `x` satisfying `E(x)=2^j` consists **exactly** of the following conditional sources:

| Branch | Source x | If and only if |
|---|---|---|
| h=1, a=1 | `2*(2^(j+2)-1)/15` | `j%4=2` |
| h=1, a=3 | `8*(2^(j+2)-13)/51` | `j%8=4` |
| **h=3, a=1** | **`2*(2^(j+4)+11)/135`** | **`j%36=18`** |
| **h=3, a=2** | **`4*(2^(j+4)-43)/243`** | **`j%162=126`** |

These sources are all genuine, pairwise distinct even nonterminal sources with odd cofactor at least five. Example: `j=126` has three legal direct sources, while `j=72` has none. There are never more than three direct even sources in this sector.

## All-exponent proof

**Possible hidden run lengths.** A target `2^j=1+3^h*w` has `3^h | 2^j-1`. By the standard 3-adic lifting identity for even j, `v3(2^j-1)=v3(j)+1=3` for `18|j`, `54∤j`. Thus `h=0,1,2,3`.

**Earlier h=0,1,2 classifications.** The two linked dossiers prove that h=0 has no legal even parent of an even power; that h=1 permits only a=1 when j%4=2, a=2 when j%18=14, or a=3 when j%8=4; and that h=2 permits only a=2 when j%54=30. The conditions for h=1,a=2 and h=2,a=2 are impossible for `18|j`. They also eliminate the exceptional odd cofactor v=3 in h<=2. Their proofs apply to all j>=18, even in the present higher-valuation sector.

**New h=3 generic equation.** Substitution of `F(x)=1+8*(2^j-1)/27` into `2F=(2^(a+1)+1)v+2a-1` gives the exact identity
```
2^(j+4) = 27*(2^(a+1)+1)*v + 54*a - 65.    (H3)
```
Write `M_a=2^(a+1)+1`, `K_a=54a-65`. For every a>=9, the odd K satisfies `1<K_a<2^a` (base a=9: 421<512, preserved by doubling). The universal signed-power gap modulo M_a, already established and Lean-certified in [Agent40's ResidueGap](../agent40-sheep-third-preimages/ResidueGap.lean), says `2^n mod M_a` cannot be an odd integer strictly between 1 and 2^a. Thus all a>=9 are impossible for every j.

For a=1..8, the **complete** power periods modulo `27*M_a`, all checked by the independent Python certificate, are:

| a | modulus | K | order of 2 | matching `n=j+4` residues |
|---|---:|---:|---:|---|
| 1 | 135 | -11 | 36 | {22} |
| 2 | 243 | 43 | 162 | {130} |
| 3 | 459 | 97 | 72 | none |
| 4 | 891 | 151 | 270 | none |
| 5 | 1755 | 205 | 36 | none |
| 6 | 3483 | 259 | 378 | {112} |
| 7 | 6939 | 313 | 144 | none |
| 8 | 13851 | 367 | 486 | none |

The a=6 solution demands `j%378=108`, hence `54|j`, forbidden here. Its smaller all-exponent necessary condition is `2^(j+4)%81=16`, equivalent to `(j+4)%54=4`. Other a can be excluded using smaller modular obstructions: a=3 modulo17 (`K=12`), a=4 modulo33 (`K=19`), a=5 modulo5 (`K=0`), a=7 modulo257 (`K=56`), and a=8 modulo171 (`K=25`). All these are impossible powers of 2 modulo their stated modulus.

**Exceptional v=3, h=3 cannot occur.** The exact equation would be
```
2^(j+3) = 81*2^a+27a+62.
```
For `a>=j-3`, the leading term already exceeds `2^(j+3)=64*2^(j-3)`. For `a<=j-4`, the right side is at most `81*2^(j-4)+27j-46`, which is less than `128*2^(j-4)` because `27j-46<47*2^(j-4)` for all j>=18 (base j=18 and straightforward induction). No integer a remains.

**Converse.** Every surviving low-a modular congruence makes the rational v integral, odd, and >=5 at the first allowed j, with monotonic growth thereafter. Direct substitution gives `F(x)-1=8*(2^j-1)/27`. The quotient `(2^j-1)/27` is odd, so the hidden valuation is **exactly h=3**, and `E(x)=2^j`. This proves sufficiency, necessity, and exhaustion.

## Evidence and significance

[PowerGateH3.lean](PowerGateH3.lean), compiled locally under Lean 4.36.0-rc2, proves the eight necessary modular rows, the a>=9 gap bound, and the a=6 sector rejection **for every exponent**; each `#print axioms` reports standard logical axioms only, with no `sorryAx`. The complete H3 theorem remains a conventional proof using these arithmetic ingredients, plus the previous source-matched h<=2 arguments.

[power_h3_verify.py](power_h3_verify.py) checks all complete periods and independently reconstructs the full legal even `E` inverse set for **67** exponents j<=1800 in this sector. These tests are finite and are not the basis for the unrestricted theorem. The underlying real six-state semantic connection is separately certified by [Agent16's source CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547).

Together, the three predecessor dossiers classify the *direct* legal even predecessors for **26/27 of even power-exponent indices** asymptotically. They do not establish genuine blank-reachability of any predecessor, and give no globally valid nonhalting theorem. The remaining whole sector `54|j` requires higher 3-adic layers; a root-sensitive obstruction to every surviving power gate is still the decisive open step.
