# Agent 16: fifth-depth symbolic Sheep inverse certificate

**2026-11-02. Intermediate mathematical research, with an exact executable modular certificate.** This strengthens the existing depth-three certificate of Agent 17 by excluding **52 more exponent residue classes modulo 5400** from the actual Sheep blank-section orbit. The original machine's halting status and BB(6) remain open. The new claim is source-program verified, not yet Lean-kernel certified, and no external novelty claim is made.

## Precise claim

For the Sheep Machine `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`, the established blank-tape acceleration enters the section at `t=5`, where `F(2^a u)` for odd `u` is:

- undefined for `u=1`, the halting target;
- `3*2^a+a+3` for `u=3`;
- `2^a*u+a+(u-1)/2` for `u>=5`.

From `t=5`, every defined return strictly increases its argument. We prove that no finite return trajectory from this genuine section entry visits `2^j` whenever `j mod 5400` belongs to the deterministic certified set of **3596** residues, whose sorted-list SHA256 is

`dc77776f9a51938d6c6e1fdb57be681477dae9b93d54fa351d4d4f9ae4b6555b`.

In comparison, Agent 17's prior depth-three certificate excludes 3544 residues (SHA256 `3501152b8f0e5feb4d45fce3505e4457264d2f6001b2ea675508abde300ccb37`). The new set difference is exactly 52 classes, all periodic modulo 2700, represented by the following 26 residues in `[0,2700)`:

```text
102, 186, 210, 318, 426, 546, 642, 726, 750, 858, 1086, 1182,
1266, 1290, 1398, 1626, 1722, 1830, 1938, 2046, 2166, 2262,
2346, 2370, 2478, 2586
```

The 23 listed residues other than `426, 2046, 2586` close already at depth four, contributing **46** new classes modulo 5400. Those three remaining residues close at depth five, contributing **6** further classes. Depth-four total: 3590/5400, digest `a428450076921a5ca8adef12ade61fcb63b421e6a9c48ae49eb12d41e8469fca`.

Thus the certified subset of halting-exponent indices has exact density **3596/5400 = 899/1350**, or approximately **66.592593%**, compared with the former **3544/5400 = 443/675**. The increment is **13/1350** of exponent classes. These are arithmetic densities, without any probabilistic interpretation for the machine's actual halting.

## Uniform reasoning, rather than a bounded simulation

This extension reuses the exact symbolic proof obligations, inverse-family representation, exceptional-branch bounds, and checked modular-period routine in [Agent 17's source](../agent17-sheep-third-generation/symbolic_sieve.py) and [proof dossier](../agent17-sheep-third-generation/SYMBOLIC-SIEVE.md). Every symbolic family is represented as `Y(j)=(2^(j+s)+b)/d`, with odd positive `d`. For a possible generic predecessor having 2-adic valuation `a`, the necessary relation is

```text
2^(j+s+1) ≡ d*(2*a-1)-2*b  (mod d*(2^(a+1)+1)).
```

An all-exponent residue gap produces a finite upper bound on `a`. For every smaller `a`, the exact congruence is checked through a complete multiplicative period, verified by `pow(2,p,m)==1`. For the special `u=3` case, each tree node receives an explicit exponential-versus-linear exclusion threshold, checked to be at most 100. At all visited nodes, `Y(j)>5` holds for `j>=100`.

The recursive certificate explores *all* eligible parent valuations. A leaf closes only if there are zero candidate parents. A closed tree cannot be visited from `5`, since its root exceeds the initial value and any first arrival must have a predecessor in the tree. Increasing the recursion from Agent 17's depth 3 to depths 4 and 5 yields the stated additional classes without changing the logical premises or weakening the checks. For `j<100`, the original script independently verifies 252 strictly increasing nonhalting section steps until the iterate exceeds `2^99`, permanently excluding every smaller power by monotonicity.

The finite computation certifies infinitely many exponents through congruence periodicity and explicit all-valuation bounds. It is not an experiment that simulates only finitely many candidate exponents.

## Reproduce

Run [`verify_deeper.py`](./verify_deeper.py) from any working directory with Python 3.10+ and SymPy 1.14, in this repository alongside the unchanged Agent 17 source. The program imports `symbolic_sieve`, reruns its section-prefix check and its exact recursive all-exponent parent test at depths 3, 4, and 5, and asserts the counts and SHA256s. It checks both newly excluded differences and their modulo-2700 periodicity. The author's independent reimplementation in `/tmp/sheep_depth_sieve.py` reproduced the depth-three original digest before the extension, then computed depth-four and depth-five totals, respectively in about 3 and 22 seconds on the local environment. This private scratch path is not a durable source; the committed `verify_deeper.py` is the reproducibility artifact.

To strengthen the evidence, independently rewrite the finite period checker in Lean and prove a certificate-soundness theorem over the imported source's `Family` type, then import the existing Agent 22 machine-to-section bridge. Neither stronger verification has yet been performed for these new 52 residues.

## Limits

The remaining **1804** residue classes modulo 5400 are not closed by this certificate. Agent 22 and Agent 39 proved that certain powers admit actual generic inverse paths of arbitrary finite depth, so increasing a single fixed depth cannot decide all remaining exponents. The ancestors on such paths are not known to occur on the real blank-start orbit. A genuine global reachable-set invariant, a resolved root, or an equivalent all-depth method is still required to settle this Sheep holdout and ultimately BB(6).


## Separately auditable six-class depth-five certificate

The six classes which first close at depth five (`j≡426,2046,2586 mod2700`) now have an independent [eight-node arithmetic proof dossier](./SIX-CLASSES.md) and [standard-library-only integer checker](./verify_six.py). The checker verifies 72 complete modular periods and 195 excluded valuation-residue cases, explicit uniform special-branch inequalities, monotone large-valuation gaps, and every symbolic family transition. It contains no SymPy dependency. This strengthens the audit trail for the deepest new classes; full Lean kernel verification of the six-class closure is still a separate task.


## 2026-11-04 original-source partial Lean verification update

A prior CI run, [41697791436](https://github.com/FlareZ123/bb6/actions/runs/41697791436), reported a type error in the two applications of `uniform_special_parent_absent` for `special_5` and `special_7` in `ExceptionalEight.lean`. Both calls omitted the explicit seventh hypothesis argument, the slope inequality. Agent16 added the two missing `(by decide)` proofs in commit [be0fa8d](https://github.com/FlareZ123/bb6/commit/be0fa8d2a61cafb840404f9f6c79e0f474e16fe9).

The immediate manual rerun [41755786111](https://github.com/FlareZ123/bb6/actions/runs/41755786111) failed during Mathlib cache extraction because the standard GitHub Ubuntu runner exceeded its filesystem quota; **no Lean compilation conclusion** followed from that run. After a targeted disk-reclamation change in the existing manual-only workflow (commit [b09714e](https://github.com/FlareZ123/bb6/commit/b09714e9a4a4b99cb0675ebbbc5b2454d67db0fe)), manual original-source run [41758334467](https://github.com/FlareZ123/bb6/actions/runs/41758334467) completed **successfully**. Its actual runner executed the pinned Cryptids source build and all relevant reconstructed Lean files. The job log explicitly shows that `SheepExceptional.special_0` through `special_7`, including the two repaired theorems, depend only on `[propext, Quot.sound]`, and `FiniteGates0` through `FiniteGates7` were compiled. Warnings about the exponentiation reduction threshold are nonfatal and do not introduce new axioms.

**Precise scope:** This source-CI success proves the eight special-predecessor *nonexistence* lemmas and compiles the generated finite modular modules. It does **not** by itself assemble a source-connected all-time no-reach theorem for all six depth-five exponent classes: the generic high-a gap, exhaustiveness-to-DAG assembly and actual-root reachability contradiction still require explicit linked Lean integration. The prior executable all-k paper certificate remains an intermediate result, and Sheep and BB(6) remain open.
