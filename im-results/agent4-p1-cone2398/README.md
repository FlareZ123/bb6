# Agent 4: P1 affine inverse cone for critical index 2398 modulo 65536

**Status as of 2026-11-02 08:49 UTC: SUCCESS.** Complete original-source Lean 4.36.0-rc2 kernel compilation and standard-axioms audit passed in [manual GitHub Actions run 41415501198](https://github.com/FlareZ123/bb6/actions/runs/41415501198), job 125178225437. This is an all-natural, genuine blank-entry infinite critical-index exclusion. It does not determine the halting status of P1 or BB(6).

## Exact target

Machine `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`, genuine accelerated blank entry `(2,1)`. Agent 4's global halting criterion, imported into the original six-state semantics by Agent 19, states that blank halting is equivalent to reaching at least one critical reset state `(2,H(n))`, where

```text
H(n) = 14 * 2^n - 2*n - 10.
```

The new source-certified theorem is

```lean
theorem BB6.Agent4Cone.no_critical_2398_mod65536 (q : Nat) :
  ¬ BB6.Agent1.Reach 2
       (14*2^(65536*q+2398)-2*(65536*q+2398)-10)
```

This residue `2398 mod 65536` is outside the previously compiled 36 closed `14 mod 16` residue families identified by Agent 28 modulo 1024, whose proposed list omits `350 mod1024` (`2398 mod1024=350`). It is also outside Agent 50's three newly source-certified `226,482,914 mod4096` index families.

## Finite exhaustive inverse proof, universally parameterized

Let `X(q)=2^(65536*q+2382)` and `t(q)=7*X(q)-(q+1)`. Then Lean proves

```text
2^(65536*q+2398) = 65536 * X(q),
H(65536*q+2398)-6 = 131072*t(q) + 126260,
t(q) + q + 1 = 7*X(q),
X(q) >= 32*(q+1).
```

The existing source theorem `critical_target_implies_three` sends a hypothetical reachable `(2,H(n))` to the odd hub `(H(n)-6,3)`. Agent 1's `GAncestor` relation exhausts the positive-output inverses of the recursive G-map. For each interior target `(b,d)`, enumerate

```text
k0 = b/4 - 1, u0 = d + b/2
u_next = (u-3)/2, k_next = k + floor(u_next/2) + 1
```

until `u` is even; the formula is only applied at provably odd `u >= 3`. Agent 50's genuine blank-reachability inverse bridge forces the prior even-left hub `(2k-4,u+4)`. Every branch terminates by one of the original source's already-proven global invariants:

1. For positive, odd second coordinate, an even first coordinate congruent to 2 modulo 4 must be exactly 2. Here every such leaf has first coordinate greater than 2.
2. For positive, even second coordinate and even first coordinate `x`, reachability implies `x+12=14*2^j`. Each such leaf has `x+12=A*t(q)+C` with `66272 <= A <= 130336` and `63834 <= C <= 125542`. A proved uniform bound shows `7*2^n < A*t(q)+C < 14*2^n`, excluding every `j`.

The entire symbolic tree has **31 interior hubs** and **62 terminal branches** (31 modular contradictions and 31 strict power gaps), maximum inverse depth seven. There are exactly 31 complete `GAncestor` inversion proofs `inv_0` … `inv_30`, each by induction over the inductive source constructors. These feed 31 `no_node_i` reachability exclusion theorems. All hypotheses and inequalities are universally quantified over `q : Nat`; no fixed numeric simulation horizon enters the Lean proof.

Independent exact-integer recursion checked the path-count and leaf classification at indices `n=2398,67934,133470,199006,330078,526686` (q=0,1,2,3,5,8). These are supplementary tests, not the universal proof.

## Proof artifact and verification

The eleven non-mock Lean source modules `PowerGap,PowerBand,Inverses,ConeNodes0..6,P1Final` are in the ordered concatenation of `cert.part00`, `cert.part01`, `cert.part02`. They form an xz-compressed tar archive encoded in base64. The exact tar.xz SHA-256 is:

```text
26c441bed288b55764c0ad5fe89b0a3c39bd134c81a05a4c90f6858e25cc7036
```

The manual-only GitHub Actions workflow `agent4-p1-cone2398.yml` verifies the archive hash, extracts all source files, compiles the **unmodified** P1 source modules `GParity,GInverse,PosEvenForm,ResetGate,P1Triple,P1ResidualArithmetic,P1ResidualReach,P1Gate`, then compiles the eleven new modules with `lean -o`. The final source prints the axioms of `BB6.Agent4Cone.no_critical_2398_mod65536`; this audit passed in run 41415501198: `BB6.Agent4Cone.no_critical_2398_mod65536` depends on exactly `[propext, Classical.choice, Quot.sound]`, without `sorryAx` or mock axioms.

The original raw six-state-machine ↔ accelerated-map equivalence was previously checked separately in Agent 19's `im-results/agent19-p1-source-bridge`; this result concerns one previously unresolved critical-index class and must not be interpreted as a P1 halting decision.

## Universal affine sieve across residual P1 index classes (computational, unformalized)

The standalone, standard-library-only `uniform_scan.py` conservatively analyzes all index residues `n=65536*q+r`, `q≥0`, in the two remaining critical sectors `r≡2` and `r≡14 (mod16)`, for `r≥21`. The code uses exact affine arithmetic `A*t+C` where `t=7*2^(65536*q+r-16)-(q+1)`; it checks uniform parity and modular conditions coefficientwise and rejects any unknown or repeated inverse chain. A lower bound `2^(65536*q+r-16) ≥ 32*(q+1)` supplies positivity and strict power gaps for all q. For a leaf expression `x+12=A*t+C`, `adjacent_power_gap` certifies inequalities `14*2^(n-1)<x+12<14*2^n` using sufficient integer coefficient conditions. Every closed certificate has exactly as many power-gap leaves as forbidden-modulo-four leaves.

A reproducible, manual-only [full-source and scanner CI run 41416935437](https://github.com/FlareZ123/bb6/actions/runs/41416935437) **passed**, reporting:

| Critical residue sector | Classes checked, r≥21 | Affine cones closed | Inverse branch nonuniform | Gap not certified |
|---|---:|---:|---:|---:|
| `r≡2 (mod16)` | 4,094 | **2,845** | 1,213 | 36 |
| `r≡14 (mod16)` | 4,095 | **2,419** | 1,594 | 82 |

Compared solely with Agent 28's 36 earlier closed `n≡14(mod16)` residue classes modulo 1024, the new scan closes **180 additional subclasses modulo 65536** which do not fall into any of those 36 modulo-1024 classes. For the hard `r≡18 or34(mod64)` subfamilies of the `r≡2(mod16)` sector, the scan closes **798** subclasses modulo 65536 (482 with r≡18 and 316 with r≡34). Some may overlap other agents' newer work; no global novelty is asserted for each. All candidate leaf gaps use the same adjacent band, and their componentwise minima/maxima still satisfy sufficient strict-band inequalities for every closed root.

**Evidence boundary:** these counts come from a deterministic Python verifier applying previously *Lean-certified* predecessor and reachability invariants symbolically. They are **computational candidate certificates**, not 5,264 newly Lean-checked theorems. Only `r=2398` from this scan has the integrated original-source proof archived in this directory. The 31/62 tree for r2398 also passed a separate independently written numeric predecessor reconstruction at six widely separated q values. The script's other closures deserve a generic kernel checker rather than thousands of nearly identical handwritten subtheorems. No infinite critical sector has been completely excluded.
