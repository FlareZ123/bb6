# Agent 40: Sheep inverse-tree synthesis (depths 3 and 4)

**Intermediate rigorously derived infinite blank-section target exclusions; the Sheep holdout and exact BB(6) remain unresolved.** All results use the published Sheep return map from the real blank-entry section t=5. The three- and four-generation inverse fibers are proved by all-valuation arithmetic in the linked detailed reports; Lean has certified the unrestricted residue-gap lemma, every large-valuation obstruction, and all necessary finite modular gates. The complete inverse and reachability theorems have not yet been jointly encoded in this local Lean development or imported into the upstream Turing-machine formalization.

| New inverse obstruction | Exponent residue classes | Density | Complete proof |
|---|---|---:|---|
| Depth 3, even parent via a=0 | j mod216∈{24,48,96,120,168} | 5/216 | [Detailed even proof](#sheep-machine-an-infinite-third-generation-inverse-obstruction) (below) |
| Depth 3, odd parent via a=1 | j mod300∈{11,31,71,91,131,191,211} | 7/300 | [ODD-CLASSES.md](./ODD-CLASSES.md) |
| Depth 3, even parent via a=1 | j mod180∈{2,22,26,38,58,62,70,98,106,110,130,142,146,166,170,178} | 16/180 | [EVEN-A1-CLASSES.md](./EVEN-A1-CLASSES.md) |
| Depth 4, all parent valuations a=0 | j mod648∈{72,144,360,504,576} | 5/648 | [FOURTH-CLASSES.md](./FOURTH-CLASSES.md) |

The classes are pairwise disjoint, including with the Agent16 prior 157/360 exclusions; total proven all-time exclusion of halting-power **exponent indices** is **9383/16200 ≈57.91975%**. This is an exact density of a union of arithmetic progressions, **not** a probability that the machine halts or a fraction of BB(6) holdouts resolved.

**Reusable Lean verification:** `ResidueGap.lean` certifies uniformly for all a,e,d the impossibility of `2^e%(2^(a+1)+1)=d` when d is odd and 1<d<2^a. `LargeValuation.lean` imports it and proves all new large-valuation third- and fourth-level exclusions. `InverseAlgebra.lean` certifies exact generic predecessor arithmetic. `ResidueCert.lean`, `OddResidueCert.lean`, `EvenA1ResidueCert.lean`, and `FourthResidueCert.lean` certify complete periodic small-valuation gates. No `sorryAx`; standard Lean axioms only. Four independent Python scripts `verify.py`, `verify_odd.py`, `verify_even_a1.py`, `verify_fourth.py` check exact inversion on bounded exponents. All have compiled or run successfully locally under Lean 4.36.0-rc2 / Python 3.

**Critical remaining obligation:** exclude **every** surviving power of two from the actual section orbit starting at 5, or produce a genuine halt. Until this is done, the undecided six-state machine and BB(6) remain open. Prior-art novelty and independent cross-review of these new families are still pending.

---

# Agent 40: Sheep Machine, third-generation source-free powers

**2026-11-02; intermediate mathematical theorem, not a BB(6) solution.** The global argument below is an elementary handwritten proof, with a standalone Lean 4.36.0-rc2 kernel certificate for the infinite fixed-modulus subcases. It does not establish the undecided machine's halting status. Novelty beyond the repository and public prior art has not been established.

## Machine and claim

Machine: `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE` (Sheep). The [Busy Beaver Wiki](https://wiki.bbchallenge.org/wiki/1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE) and [DeepMind's Lean-certified reduction](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_HHH1LE.lean) establish the actual blank section starts at **t=5** and has return map F on t≥3. Write t=2^a·u, u odd:

- u=1: halt (F undefined);
- u=3: F(t)=t+a+3;
- u≥5: F(t)=t+a+(u−1)/2.

Let `R={24,48,96,120,168}`. **Theorem:** for every `j mod 216 ∈ R`, put `p=(2^(j+1)+1)/3` and `x=(2^(j+2)+5)/9`. These are integers with p,x>5. There are **exactly** the following inverse fibers among all t≥3:

`F⁻¹(2^j)={p}`; `F⁻¹(p)={x}`; `F⁻¹(x)=∅`.

Therefore the actual section orbit beginning at t=5 **never visits 2^j**, for every exponent in those five infinite arithmetic progressions. This is a rigorous reverse-reachability obstruction on the *actual blank section*, independent of any finite simulated prefix.

These classes are disjoint from the earlier 157/360 excluded-exponent density proved in `im-results/agent15-sheep-backwards/` and `im-results/agent16-sheep-power-preimages/`: their residues modulo 72 are 24 or 48, whereas earlier excluded even exponents have residues 8,16,40,56,64. The exact combined excluded density is **157/360+5/216 = 62/135 ≈45.9259%** of target exponents. This is no probability of halting, and leaves infinitely many power-of-two targets unresolved.

## Complete proof

**Residue gap.** Set M=2^(a+1)+1. If e=q(a+1)+r with 0≤r≤a, then 2^e≡(−1)^q·2^r (mod M). The least nonnegative residues are 2^r and M−2^r. The former is 1 or even. The latter is at least 2^a+1. Consequently, for **every** e, `2^e mod M` cannot equal any odd integer D with `1<D<2^a`. This is a uniform lemma in both exponent and valuation.

For the generic branch u≥5 we have the exact identity

`2F(2^a u)=(2^(a+1)+1)u+2a−1.` (G)

The exceptional branch u=3 never produces a power of two: its values for a=0,1,2 are 6,10,17; for a≥3 its output 3·2^a+a+3 is strictly between 2^(a+1) and 2^(a+2). It also never produces p or x when j≥24. Indeed `a↦3·2^a+a+3` is increasing, and

`3·2^(j−3)+j < p,x < 3·2^(j−2).`

The left differences p−(3·2^(j−3)+j) and x−(3·2^(j−3)+j) are respectively `(7/24)2^j+1/3−j` and `(5/72)2^j+5/9−j`; both are positive at j=24 and increase for all subsequent j. The right inequalities are immediate for j≥24. Hence when a≤j−3 the exceptional output is below p and x, while when a≥j−2 it is above both. Sources with u=1 have no F-successor.

**Level 1.** Equation F(2^a u)=2^j, with u≥5 odd, is

`2^(j+1)=(2^(a+1)+1)u+2a−1.` (1)

For a≥2, `D=2a−1` is odd with 1<D<2^a, verified at a=2 and preserved inductively. Reduce (1) modulo M and use the residue gap. For a=1, (1) demands `2^(j+1)≡1 (mod 5)`, whereas j is divisible by 24 and the actual residue is 2. For a=0 the unique solution is u=p; it is odd and at least 5 because j is a positive even exponent. Direct substitution verifies F(p)=2^j. Thus the first fiber is exactly {p}.

**Level 2.** Equation F(2^a u)=p becomes

`2^(j+2)+5−6a = 3(2^(a+1)+1)u.` (2)

For a≥5 the required residue `D=6a−5` is odd with 1<D<2^a, starting at a=5 and persisting by induction; the gap excludes it. For a=1,2,3,4 the congruences obtained from (2) are:

| a | test modulus | required power `2^(j+2)` | actual or structural obstruction |
|---|---|---|---|
| 1 | 5 | 1 | 4 |
| 2 | 27 | 7 | 13 or 22 |
| 3 | 17 | 13 | 4 |
| 4 | 11 | 8 | even powers of two modulo 11 lie in {1,3,4,5,9} |

For a=0 the unique solution is u=x. Since j is a multiple of six, `2^(j+2)+5 ≡ 9 (mod 18)`, making x an odd integer. Directly F(x)=p. Thus the second fiber is exactly {x}.

**Level 3.** Equation F(2^a u)=x becomes

`2^(j+3)+19−18a = 9(2^(a+1)+1)u.` (3)

For a≥7 the required residue D=18a−19 is odd with 1<D<2^a. The base a=7 has 107<128; if the upper bound holds at a≥7, then adding 18 is less than doubling 2^a. Hence the gap forbids every a≥7. For 0≤a≤6 a divisor of the modulus on the right of (3) gives:

| a | test modulus | required `2^(j+3)` | actual residue or obstruction |
|---|---|---|---|
| 0 | 27 | 8 | 26 or 17 |
| 1 | 5 | 4 | 3 |
| 2 | 81 | 17 | 80,71,53,44,26 |
| 3 | 17 | 1 | 8 |
| 4 | 11 | 9 | odd powers of two modulo 11 lie in {2,6,7,8,10} |
| 5 | 5 | 1 | 3 |
| 6 | 27 | 8 | 26 or 17 |

Every row contradicts (3). This table is **uniform in all j∈E**, since 216 is a multiple of the orders of 2 modulo 5,17,27,81; and the order modulo 11 is ten, allowing the parity exclusion. For the five base residues j=24,48,96,120,168 respectively, `2^(j+3) mod81` equals 80,71,53,44,26. The Lean file independently proves all fixed-modulus inequalities for arbitrary q≥0 via `2^(r+216q)`, plus the two parity properties modulo 11 for arbitrary exponents. Combining these subcases and the exceptional-branch exclusion establishes **F⁻¹(x)=∅**.

The section begins at t=5, whereas x>5. Any visit to x would require an incoming F-edge, which we proved nonexistent. Accordingly the section never visits x, then cannot visit p, then cannot visit 2^j. QED.

## Verification and limitations

- `ResidueCert.lean`: standalone, checks under Lean 4.36.0-rc2. `#print axioms` on `smallGates`, `oddPow11`, `evenPow11` reports `propext` and `Quot.sound`, with **no sorryAx**. This certificate covers the infinite modular table and parity parts, while the residue-gap and exceptional-branch inequalities remain elementary hand-proved lemmas in this note.
- `verify.py`: independent exact inverse enumeration for 29 matching exponents through 1200 and 500 modular cases, with success outputs.
- The published machine-to-section proof is upstream; this file does not import it into the local standalone Lean module.
- The theorem decides five infinite **target exponent classes**, not a single six-state machine's overall halting status. For further work, investigate deeper inverse trees on the still-allowed exponent classes or a forward invariant of the actual trajectory from t=5.

**Related previous work:** `im-results/agent14-sheep-preimages/`, `im-results/agent15-sheep-backwards/`, `im-results/agent16-sheep-power-preimages/`.
