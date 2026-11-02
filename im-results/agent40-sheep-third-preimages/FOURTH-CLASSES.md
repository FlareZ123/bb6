# Fourth-generation inverse-tree obstruction for the Sheep Machine

**Agent 40, 2026-11-02. Intermediate all-exponent theorem; BB(6) remains open.** This result extends the three-layer reverse-tree theorems in this directory by one layer, with complete handwritten arithmetic proof, independent exact inverse tests, and Lean 4.36.0-rc2 kernel checks for all modular and large-valuation exclusions. The upstream machine-to-return-map correctness is cited rather than imported here.

## Theorem and exact inverse tree

The Sheep Machine is `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`. Its published blank-reachable return section starts at **t=5** and follows the partial map F:

- t=2^a u with u odd; if u=1, F is undefined (halts);
- if u=3, F(t)=t+a+3;
- if u≥5, F(t)=t+a+(u−1)/2.

For every natural j such that

`j mod 648 ∈ {72,144,360,504,576}`,

define

`p=(2^(j+1)+1)/3`, `x=(2^(j+2)+5)/9`, `y=(2^(j+3)+19)/27`.

These are positive odd integers, each greater than five. Their **complete inverse fibers among every t≥3** are:

`F⁻¹(2^j)={p}`, `F⁻¹(p)={x}`, `F⁻¹(x)={y}`, `F⁻¹(y)=∅`.

Consequently the actual section trajectory from t=5 **never reaches 2^j** for any j in these five infinite residue classes. This is a mathematical all-time exclusion, independent of finite forward simulation.

These five classes have natural density 5/648 among exponent indices and are disjoint from the preceding 57.148% exclusions: all j are multiples of 72, whereas prior excluded even classes have residues 8,16,40,56,64 mod72 or 24,48,96,120,168 mod216 or 2 mod4. The earlier odd classes are disjoint by parity. The combined excluded exponent-index density therefore increases to

`157/360 + 5/216 + 7/300 + 16/180 + 5/648 = 9383/16200 ≈ 57.919753%.`

This does **not** imply that the machine runs forever, nor improve the known BB(6) lower or upper bound.

## Exact algebra and uniform gap theorem

For generic odd part u≥5, the complete inverse equation is

`2F(2^a u)=(2^(a+1)+1)u+2a−1.` (G)

A fully Lean-proved, unrestricted residue-gap lemma in `ResidueGap.lean` states that for every a,e and odd D with 1<D<2^a:

`2^e % (2^(a+1)+1) ≠ D.`

Its Lean proof handles arbitrary exponents by `2^(a+1)≡−1` modulo `2^(a+1)+1`. The 2^e residues are exactly ±2^r for 0≤r≤a. Positive representatives are 1 or even; negative representatives exceed 2^a. The necessary exponential-versus-linear bounds are also kernel checked in `LargeValuation.lean`, now including the fourth-level D=54a−65 gate for a≥9.

For all j in the five classes, j is a multiple of 72, hence j≡0 modulo 4,6,8,12,18,24. The Lean certificate `FourthResidueCert.lean` proves every modular inequality in the cases below for all such j. It reduces each exponent to its residue modulo a finite period dividing 648 and checks all five possible base residues, plus unrestricted universal modulo 11,43,257 lemmas. All its public printed theorems report only standard Lean axioms `propext` and `Quot.sound` with no `sorryAx`.

**Exceptional u=3 branch.** Its image is f(a)=3·2^a+a+3, increasing in a and never a power of two (values 6,10,17 for a=0,1,2, then strictly between 2^(a+1) and 2^(a+2)). It cannot equal p or x because for j≥72,

`f(j−3)<p,x<3·2^(j−2)<f(j−2)`.

The strict lower differences are `p−f(j−3)=(7/24)2^j+1/3−j` and `x−f(j−3)=(5/72)2^j+5/9−j`, both positive from j=72 and increasing thereafter. It cannot equal y either:

`f(j−4)<y<3·2^(j−3)<f(j−3)`,

as `y−f(j−4)=(47/432)2^j+46/27−j` is positive for j≥72. Thus all incoming edges at the three parent levels arise from the generic u≥5 branch. Sources with u=1 have no outgoing edge.

## First and second parent fibers

Equation (G) for target 2^j is

`2^(j+1)=(2^(a+1)+1)u+2a−1.`

For a≥2, D=2a−1 is odd and lies strictly between 1 and 2^a. Gap lemma excludes it. At a=1, the necessary congruence `2^(j+1)≡1 mod5` fails because j multiple72 yields residue2. At a=0 the unique quotient is p, an odd integer≥5. F(p)=2^j by direct substitution. Therefore F⁻¹(2^j)={p}.

For target p, multiplying (G) by three gives

`2^(j+2)+5−6a=3(2^(a+1)+1)u.` (2)

At a≥5, D=6a−5 is odd in (1,2^a), excluded by the gap lemma. At a=1,2,3,4, the necessary congruences respectively are `2^(j+2)≡1 mod5`, `≡7 mod27`, `≡13 mod17`, or `≡8 mod11`; the first three are explicitly excluded by `FourthResidueCert.smallGates_all`, and the last is excluded because j+2 is even and even powers modulo11 are {1,3,4,5,9}. At a=0, equation (2) yields the sole possible u=x. Since j multiple72, 2^(j+2)≡4 mod9, so x is integral and odd, with x≥5; substitution verifies F(x)=p. Hence F⁻¹(p)={x}.

## Third parent fiber

For target x, multiplying (G) by nine yields

`2^(j+3)+19−18a=9(2^(a+1)+1)u.` (3)

At a≥7, D=18a−19 is odd in (1,2^a), excluded by the gap lemma; this is formally proved by `LargeValuation.evenA0_third_large`. At a=1,...,6:

| a | necessary residue | obstruction |
|---:|---|---|
| 1 | `2^(j+3)≡4(mod5)` | actual 3 |
| 2 | `2^(j+3)≡17(mod81)` | actual 8,35 or62 across these residue classes |
| 3 | `2^(j+3)≡1(mod17)` | actual 8 |
| 4 | `2^(j+3)≡9(mod11)` | exponent j+3 is odd; odd powers modulo11 exclude 9 |
| 5 | `2^(j+3)≡1(mod5)` | actual 3 |
| 6 | `2^(j+3)≡3(mod43)` | no power of two is 3 modulo43 |

The finite gates and universal obstructions are Lean checked. At a=0, equation (3) yields u=y. For j multiple72, `2^(j+3)≡8(mod27)`; thus y is an odd integer≥5, and direct substitution verifies F(y)=x. Therefore F⁻¹(x)={y}.

## Fourth fiber is empty

For target y, multiplying (G) by 27 yields

`2^(j+4)+65−54a=27(2^(a+1)+1)u.` (4)

Thus the necessary condition is `2^(j+4)≡54a−65 (mod 27(2^(a+1)+1))`.

At a≥9, D=54a−65 is odd and 1<D<2^a. Base case a=9 has D=421<512, and the inequality persists inductively because D increases by 54 as 2^a doubles. The exact universal exclusion `2^e % (2^(a+1)+1) ≠ 54a−65` for a≥9 is proved in `LargeValuation.fourth_evenA0_large` using `ResidueGap.gap`.

At a=0,...,8 the full necessary congruences and contradictions are:

| a | modulus dividing 27(2^(a+1)+1) | required residue | reason impossible |
|---:|---:|---:|---|
| 0 | 81 | 16 | actual `2^(j+4)%81` is 43 or 70 |
| 1 | 5 | 4 | actual 1 |
| 2 | 243 | 43 | actual is 205,151,232,124 or70 |
| 3 | 17 | 12 | no power of two has residue12 modulo17 |
| 4 | 11 | 8 | j+4 even; even powers of two modulo11 exclude 8 |
| 5 | 13 | 10 | j+4≡4(mod12), actual `2^4%13=3` |
| 6 | 81 | 16 | same exclusion as a=0 |
| 7 | 257 | 56 | 2^8≡−1 modulo257; residues ±2^r, 0≤r≤7, exclude56 |
| 8 | 19 | 6 | j+4≡4(mod18), actual `2^4%19=16` |

Every row is proved for **all j** in the listed residue classes by `FourthResidueCert.lean`; there are no unbounded or unchecked small valuations. Together with the exceptional-branch argument and the universal a≥9 gate, equation (4) is impossible for any predecessor, so F⁻¹(y)=∅.

Since y>5 and the actual section starts at 5, a visit to y would require a predecessor, which cannot exist. Hence x, p and 2^j are likewise unreachable from the true blank section, proving the theorem.

## Reproduction, scope, next research

`FourthResidueCert.lean` compiles standalone under Lean 4.36.0-rc2, with no sorryAx. `LargeValuation.lean` imports `ResidueGap.lean` and proves the universal large-a theorem. The inverse identities and exceptional-branch bounds above are handwritten rather than fully Lean-encoded, and the upstream machine-to-section equivalence is taken from DeepMind's cited formal library. `verify_fourth.py` independently enumerates exact incoming edges at all four levels for **23 matching exponents through j=3000**, plus **1,000 full modular-gate instances**; all passed.

The important open obligation remains determining whether the actual section from 5 reaches **any of the remaining infinitely many powers of two**. A sequence of target-density exclusions is only a partial approach to this unresolved six-state holdout and cannot establish the exact value of BB(6).
