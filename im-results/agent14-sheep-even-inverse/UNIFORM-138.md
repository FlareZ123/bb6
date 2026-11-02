# Uniform Sheep even-return exclusion: exponent 138 modulo 4860

Agent 14, 2026-11-02. **Intermediate mathematical finding.** The proof is a universal arithmetic argument with a standard-library-only executable modular certificate in [uniform_138.py](./uniform_138.py). It uses the original-machine authenticated even-return reduction of [Agent 16](../agent16-sheep-even-return/README.md), verified by CI 41505950547. The Sheep machine and BB(6) remain unresolved. No external novelty claim is made.

## Theorem

Let E be the actual deterministic even-return graph of the six-state Sheep machine, beginning at the authentic entry 10. For every natural k, the exponent j=138+4860k is excluded:

    not (SheepEven.EvenReach 10 (2^j)).

This rules out one infinite family of candidate halting gates on the **actual** blank-start orbit. The original-machine halting condition still allows other exponents.

## Complete inverse equations

For even t=2^a*v, a>=1, odd v>=3, let z=F(t), where F is the independently certified section return:

    F(3*2^a)=3*2^a+a+3;
    F(2^a*v)=2^a*v+a+(v-1)/2, for odd v>=5.

The even successor is E(t)=1+3^h*u, where z-1=2^h*u, u odd. For any rational symbolic target Y=(2^(j+s)+b)/d with d positive odd, an E-predecessor requires

    3^h | (Y-1)
    D=d*3^h; C=2^h*(b-d)+D
    z=(2^(j+s+h)+C)/D.

In the exceptional v=3 case, z=3*2^a+a+3. In the generic v>=5 case,

    N=2^(j+s+h+1)+2*C-D*(2*a-1)
    T=D*(2^(a+1)+1)
    v=N/T must be odd, v>=5
    t=(2^(j+s+h+1+a)+2^a*(2*C-D*(2*a-1)))/T.

Consequently a generic parent can occur only when both congruences hold:

    2^(j+s)+b-d == 0 (mod d*3^h);
    N == T (mod 2*T).

The second condition enforces that the quotient v is odd. Treating these two necessary congruences as sufficient candidates only enlarges the inverse tree, which is safe for a nonreachability proof.

## Uniform bounds that make exhaustive modular checking finite

For each node choose H such that d*3^H never divides 2^(j+s)+b-d for j=138+4860k. This rules out all h>=H. The checker exhausts the complete multiplicative period of 2 modulo each odd modulus.

For each h, define Q_a=D*(2*a-1)-2*C, an odd number. The generic parent equation forces 2^(j+s+h+1) == Q_a modulo 2^(a+1)+1. Every positive power of 2 modulo 2^(a+1)+1 is congruent to either +2^r or -2^r, 0<=r<=a. Hence an odd integer 1<Q_a<2^a is impossible as such a residue. To prove this for *all* a>=A, the checker verifies at A:

    1<Q_A<2^A; 2^A>2*D.

The inequalities propagate: Q_(a+1)=Q_a+2D while 2^(a+1) doubles.

Every exceptional v=3 candidate requires, for n=j+s+h,

    2^n=3D*2^a+D*(a+3)-C.

Put c=3D, e=bit_length(c), and choose n0 with

    n0>=e+2,
    (2^e-c)*2^(n0-e)>D*(n0+3)+abs(C),
    2^(n0-e)>2D,
    D*(n0-e+4)>=C.

These conditions, verified by the checker, persist as n grows. When a<=n-e, the gap 2^n-c*2^a is strictly too large. For a>=n-e+1, the c*2^a term already exceeds 2^n and the remaining term is nonnegative. Therefore no exceptional source exists when n>=n0. Every symbolic node below satisfies j+s+h>=n0 for j>=138.

For remaining 0<=h<H, 1<=a<A, both congruences are tested over **every** k in one complete period. The period modulo 2*T equals the order of 2 modulo the odd integer T for positive exponents, because powers of 2 are even. All periods are computed by exact prime factorization and divisor tests. Maximum period visited in the small-a checks is 13.

## Exhaustive three-node certificate

| Target | H | Successive A cutoffs | Successive n0 cutoffs | Surviving (h,a) |
|---|---:|---|---|---|
| Y0=2^j | 3 | 2,5,7 | 6,7,10 | (1,1), (2,2) |
| Y1=(2^(j+3)-2)/15 | 4 | 8,10,12,14 | 11,15,18,21 | none |
| Y2=(2^(j+5)-68)/81 | 2 | 11,13 | 16,19 | none |

The surviving root predecessors are exactly Y1 and Y2. Both have **no possible E-predecessor** for any j in this residue family. They are integers greater than 10 for every k, and the root is also different from 10. Consequently no orbit from 10 can ever arrive at a root 2^j, which proves the theorem.

## Reproduce and independently audit

Run `python uniform_138.py` with Python 3.10 or newer and no third-party dependencies. The program asserts every complete modular period, all all-valuation gap and exceptional inequalities, and the exact two predecessor families. It prints PASS. An independent direct integer inverse enumerator [exact_inverse.py](./exact_inverse.py) corroborates for j=138,4998,9858: each target has exactly the predicted two E-parents, and each parent has no E-parent. Five ordinary section-backward levels do not close these examples, while two E-backward levels do.

**Evidence limits:** The modular proof is not yet re-expressed as a single Lean theorem; the authentic E-to-original-machine bridge is already Lean source checked by Agent 16. Full formalization, cross-review of all inequalities, and an external literature novelty audit remain open. Keep this result in im-results until those checks.

## Supplementary Lean verification (November 2, 2026)

The following obligations are now Lean 4.36.0-rc2 kernel checked, with only standard axioms `propext`/`Quot.sound` and no `sorryAx`:

- [EvenPeriod.lean](./EvenPeriod.lean): arbitrary-index modular-period rules, preservation of parity-sensitive residues modulo twice an odd modulus, general exact finite-period exclusion, and one explicit inverse exclusion.
- [UniformH.lean](./UniformH.lean): all twelve infinite-k high-h nondivisibility cutoffs for the four certified exponent families.
- [HighBound.lean](./HighBound.lean): uniform induction proving every large-valuation residue falls into the strict impossible interval, including **all nine** `(h,node)` cutoffs for the r=138 tree.
- [ExceptionalBound.lean](./ExceptionalBound.lean): kernel proof that an exponential-over-linear comparison remains valid for every larger exponent, a supporting lemma for excluding special odd-part-three sources.
- [generate_low138.py](./generate_low138.py): deterministic generator for `Low138.lean`, a **181,253-byte, 71-theorem** Lean source certifying every remaining low-valuation generic inverse disqualification for r=138. SHA256 `5f9c2737aa168b3eee0ec33e81d078f8afdb3151f3f12508e721019b756a94eb`. The generated file compiled successfully locally (27.4 seconds, ~1.1 GB peak RSS), with all 71 axiom audits reporting only standard axioms.

To reproduce the last file, generate `Low138.lean` with Python 3.10+, the standard `uniform_138.py` module and the `filelock` library, compile `EvenPeriod.lean` to a Lean object file, and compile the generated `Low138.lean` with that object on the Lean library path. All arithmetic is exact and the generated source hash is asserted before writing.

The end-to-end proof connecting the Lean low-a and high-a arithmetic with the original section map is still a **separate unproved Lean integration task**. The exceptional-source all-a proof is written in this note and checked numerically for each base threshold, while only its general growth sublemma is currently kernel checked. The present status is therefore a mixed written proof, executable arithmetic certificate, and substantial independently checked Lean arithmetic components.
