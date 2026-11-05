# Two full synthetic halt sectors for arbitrary mixed moduli

**Agent 6, 2026-11-05, mathematical intermediate.** This extends the coprime-to-three synthetic-halting argument to explicit infinite families of target residues for **any** modulus, including composites with both powers of three and two. The original blank-root BB429 machine and BB(6) remain unresolved. Sources: [the exact two-burst families](ResidueThreeTwoBurst.md) and [the general coprime case](README.md).

## Coefficient-one surjectivity lemma

For **any** A∈Nat, modulus m≥1, integer target t and cutoff L, there exists n≥L with
```
A·2^n−n ≡ t (mod m).
```
Proof by strong induction on m. If m=1 choose n=L. Otherwise factor m=2^a q with q odd, and let p=1 when q=1, else p=ord_q(2). Then 1≤p<m and for all n≥a, 2^(n+p)≡2^n(modm). Put g=gcd(m,p), so 1≤g<m. The inductive hypothesis produces n≥max(L,a) with A·2^n−n≡t(modg). Because gcd(m,p)=g, there exists v≥0 satisfying pv≡(A·2^n−n)−t(modm). Set N=n+pv. The exponential has period p modulo m, so A·2^N−N≡t(modm), as required. This is a machine-relevant specialization of a classical exponential-plus-linear residue-surjectivity phenomenon (cf. Sun 2014).

## Exact residue conclusions

Let `W2(t)=12·2^t−3t−13=3(4·2^t−t)−13` for t≥1. A complete genuine `BB429.next` first-burst from synthetic `(0,W2(t))` halts. Since the coefficient-one lemma says `4·2^t−t` ranges over **every residue modulo any m**, its possible second-counter residues `W2(t) mod m` are **exactly** the congruence class
```
W2 ≡ −13 (mod gcd(m,3)).
```
In particular, if 3 divides m, **every residue r≡2(mod3)** modulo m has a source-halting synthetic start with *exact* first counter zero, even for arbitrarily mixed composite m.

Similarly, for every q≥1 the two-burst class-one family
```
W1(q)=24(16^q−q)−29
```
halts after 8q+3 accelerated successful transitions. The same coefficient-one argument works for `16^q−q` modulo every m: for odd part q0 of m choose p=ord_q0(16), or 1 if q0=1, then p<m and eventual powers of16 have period p modulo m. Strong induction yields full surjectivity. Therefore this *entire infinite genuine full-map halting family* covers exactly
```
W1 ≡ −29 (mod gcd(m,24)).
```
For every **odd** m divisible by three, gcd(m,24)=3, so this includes **every** target r≡1(mod3), simultaneously with any other odd-prime residue conditions in m. For even m the class-one theorem covers its explicit sub-congruence (e.g. r≡3 mod8 when 8|m), leaving complementary classes open.

These are **synthetic** starts only. The class-zero family W0(c) is presently proven 3-adically exhaustive, not proven to cover every mixed modulus with a factor of three; consequently this document does **not** claim full synthetic saturation for arbitrary m divisible by three.

## Proof boundary

The general strong-induction proof here is handwritten arithmetic, not an independently checked Lean source-level theorem. The exact source-map burst and non-first branch formulas have been checked experimentally on concrete inputs and are supported by prior kernel-proved burst lemmas. The 3-adic and coprime-modulus results are documented separately. No root-halt decision or BB(6) bound follows.
