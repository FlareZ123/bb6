# Arbitrary-modulus obstruction to fixed-depth Sheep inverse-tree closure

**Status:** intermediate, exact mathematical corollary of Agent 39's source-checked zero-valuation inverse-chain classification and the generalized Chinese remainder theorem. It supplies no blank-orbit reachability invariant, no resolution of the Sheep Machine, and no BB(6) bound. The standalone arithmetic necessary direction is compiled by Lean 4.36.0-rc2; the complete new CRT synthesis below has a conventional written proof and executable Python checks, but is **not itself fully Lean formalized**. Do not move this into `results/`.

Machine: `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`, genuine blank return section `t=5`. Every defined section step is increasing. The halting target is a power `2^j`. For `h>=1` the term *zero-valuation inverse corridor of length h* means h **actual** generic return edges all having valuation `a=0`, traversed backwards from the target. Synthetic starting vertices of these paths are not known blank-reachable.

## Theorem: exact finite-depth compatibility for every modulus

Fix any modulus `M>=1`, residue `0<=r<M`, and desired inverse depth `h>=1`. Define `D_h=2*3^(h-1)` and `g_h=gcd(M,D_h)`. Then the following are equivalent:

1. There exists an exponent `j>=3` with `j mod M=r` and a genuine zero-valuation Sheep inverse corridor of length `h` ending at `2^j`.
2. `g_h` divides `r`.

Moreover, when this holds, there are infinitely many such exponents `j`, unbounded above. Thus no finite depth-h backward proof that relies *only on absence of inverse predecessors* can close **every** target in this residue class at once.

**Proof.** Agent 39's source-level `PowerCorridor.lean` gives the exact all-natural iff

    length-h zero-valuation inverse corridor into 2^j  <=>  2*3^(h-1) divides j, for j>=3.

Hence the question is the pair of linear congruences `j≡r (mod M)` and `j≡0 (mod D_h)`. The generalized CRT states that the pair is soluble iff `gcd(M,D_h)|r`. Every solution is congruent to one base solution modulo `lcm(M,D_h)`, so there are arbitrarily large solutions satisfying `j>=3`. For explicit witnesses, let `g=g_h`, `m=M/g`, `d=D_h/g`, `s=r/g`. If `g|r`, the coprime integers `m,d` give `k=s*d^(-1) (mod m)` (when `m=1`, choose `k=0`), and `j=D_h*k+lcm(M,D_h)*q` for sufficiently large nonnegative `q`. Necessity of the gcd divisibility is also proved without Mathlib in `ModulusNecessary.lean`, kernel-audited with `[propext, Quot.sound]` in the local toolchain.

## Theorem: exactly which classes obstruct **every** fixed depth

Write `beta=v_3(M)` for the greatest exponent with `3^beta|M`, and define

    C(M) = 3^beta * gcd(M,2).

For `0<=r<M`, the following are equivalent:

1. For **every** finite inverse depth `h>=1`, some target exponent `j>=3`, `j≡r (mod M)`, has a genuine length-h zero-valuation inverse corridor.
2. `C(M)|r`.

Proof: `gcd(M,2*3^(h-1))=gcd(M,2)*3^min(beta,h-1)` increases in divisibility to the stable factor `C(M)` once `h>=beta+1`. Apply the preceding iff for each h. There are **exactly `M/C(M)`** residue classes satisfying this all-depth obstruction. The quantifiers are crucial: the witness exponent may depend on `h`; no single finite exponent supports corridors of all lengths.

### Examples and research implications

| Modulus | Persistent depth-obstructed residue classes | Reason |
|---|---:|---|
| 7 | 7 of 7 | Coprime to 6; every class admits arbitrarily deep synthetic chains |
| 100 | 50 of 100 | Even residue classes |
| 54 | 1 of 54 | Only residue 0 |
| 5400 | 100 of 5400 | Exactly the multiples of 54, reproducing Agent 39 |
| 10800 | 200 of 10800 | Still multiples of 54 |
| 16200 | 100 of 16200 | Multiples of 162 |

**Practical limitation on modular inverse sieves:** If `gcd(M,6)=1`, no residue class of this modulus can be uniformly closed by any fixed finite-depth inverse tree whose leaves assert missing predecessors. For every other modulus at least the residue-zero class is obstructed. Adding factors coprime to 6 changes the count but not the obstructed fraction; powers of 2 beyond the first do not lower that fraction. Increasing the 3-adic valuation of the modulus lowers the obstructed fraction by a factor of 3 per power, but never removes every obstruction. This is an obstruction to a restricted proof method, not to nonhalting itself or to stronger reachability-based inversions.

## Reproduction, dependencies, and audit

- Source-checked original Sheep counter/section bridge, zero-valuation inverse chains, and exact order of 2 modulo powers of 3: `im-results/agent39-sheep-zero-ancestry/{ZeroAncestry.lean,ZeroAncestryBridge.lean,ThreeAdicOrder.lean,PowerCorridor.lean,ActualResidue.lean}`, successful full-source [CI 41431834393](https://github.com/FlareZ123/bb6/actions/runs/41431834393). The arbitrary-modulus residue-zero construction by Agent 22 precedes this extension: `im-results/agent22-sheep-infinite-inverse/GeneralAncestry.lean`.
- `ModulusNecessary.lean`: machine-independent necessary direction of the modular criterion, compiled locally with Lean 4.36.0-rc2, audited axioms `[propext, Quot.sound]`. The CRT sufficiency and the stabilized-factor count are written proofs, **not** kernel-checked here.
- `modulus_corridors.py`: deterministic exact integer CRT witness construction and genuine Sheep return-edge cross-check. Python 3.11, no third-party dependencies: `python modulus_corridors.py`. Local run: `PASS: 114030 residue/depth CRT cases; 89752 genuine Sheep edges checked`. It tests all `1<=M<=180`, all residues and depths 1..7, verifies modular powers modulo `3^h` and tests the actual source and target counter edges where `j<=2000`.

**Next useful research direction:** derive an all-time *forward* invariant from the actual section entry `5` that excludes the long synthetic source vertices, or replace finite-depth leaf-exhaustion with a well-founded/global argument. Increasing modulus and bounded-depth certificate throughput alone is mathematically incapable of resolving the listed persistent classes.

## Additional general symbolic inverse tools (newer than the arbitrary-modulus criterion)

**Kernel-certified all-exponent generic residue gap:** [GeneralOddGap.lean](./GeneralOddGap.lean) now proves `BB6Sheep17Gap.no_power_signed_gap`, for **all** natural `a,n` and integers `0<c<K` with odd `K`. If

`c*(c+K)+K < 2^(a+1)+1`,

then `2^(a+1)+1` divides neither `c*2^n-K` nor `c*2^n+K`. The theorem uses a strong-induction proof in the exponent, explicit positive and negative modular cases, exact integer division and a strict gap bound, with no Mathlib or asserted period oracle. **Local Lean 4.36.0-rc2 compiled with no admitted proofs; `#print axioms` lists only `[propext, Classical.choice, Quot.sound]`.** The checked source is a new formal strengthening of the mathematical gap underpinning [GENERAL-TAIL.md](./GENERAL-TAIL.md), which bounds generic predecessors of arbitrary positive-coefficient symbolic families. Independently checked abstract monotone propagation is in [GeneralTailPersistence.lean](./GeneralTailPersistence.lean). The combined theorem and bound are source-level arithmetic tools; the complete symbolic parent/simulator relation is not yet fully kernel-composed for this general coefficient language.

**Uniform exceptional-branch elimination:** [EXCEPTIONAL-TAIL.md](./EXCEPTIONAL-TAIL.md) gives a general exact constructive all-exponent cutoff `J` such that, for all `j>=J`, no Sheep exceptional predecessor `3*2^a` reaches target `(c*2^(j+s)+b)/d`. The proof handles all `a` by high/low/near-exponent comparisons, including resonance of the exponential leading terms. No parity restriction on `d` is required. [exceptional_uniform.py](./exceptional_uniform.py) passed **4,000 family tests and 651,923 exact inequalities**. The proof is currently written and computationally corroborated, not Lean-kernel verified.

Combining these results gives a general **finite-branching inverse-family framework above an explicit exponent threshold**. It does not provide a closed blank-reachable-set invariant or decide the Sheep holdout. Reusable published-in-repo prior work on exact zero-valuation inverse corridors (Agents 22/39) means unbounded inverse depths remain a genuine obstruction.
