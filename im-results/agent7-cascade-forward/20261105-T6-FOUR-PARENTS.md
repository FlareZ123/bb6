# #746 quantified valuation-six reset inverse and four-parent candidate

Agent 7, 2026-11-05. This is **intermediate mathematics**, not a machine-wide halting theorem or a new BB(6) bound.

## The source-shaped result

The already source-certified `CascadeResetInverse.ResetParent` is the complete algebraic characterization of genuine first-reset edges. For near-top target `u+A=4*2^n`, `n>=10`, `64A+164<=13*2^n`, the new `FirstForkSix.lean` proves that if `2187 | (2u+5)`, then the odd valuation `t=6` has an exact predecessor

`P6(n,u) = 128 * ((2u+5)/2187) - 8*2^(n-5) - (n-5) - 5.`

The proof checks the genuine odd dyadic inverse band with `k=n-5`, rather than assuming a synthetic short cut. It supplements earlier `t=1,3` witnesses. `FirstForkSixResidues.lean` proves that this phenomenon holds for **every** `n>=10` in fatal index classes `n mod 4374 ∈ {491,3208}`, and for the second forced even fatal ancestor when `n mod 4374 ∈ {83,1906}`. These arithmetic assertions were independently reconstructed and kernel-checked in local self-contained Lean 4.36.0-rc2 stubs with only `[propext,Quot.sound]`.

`FirstForkOddValuationSix.lean` extends near-top odd-valuation exclusion to `t ∈ {1,3,6}` when `(2u+5)%6561 != 0`, using prior certified gap lemmas for t0,t2,t4,t5. `FirstForkExactFour.lean` gives a proposed **complete iff**, with explicit even parent plus odd parents t1,t3,t6. `FirstForkRootFour.lean` transports that complete classifier to **authentic blank-reset-root reachability equivalences**, including the two infinite families above subject to the nondivisibility-by-6561 hypothesis.

## Verification status

The first six earlier near-top fork modules were compiled against unmodified checked-in source dependencies in manual [Lean CI 41966512900](https://github.com/FlareZ123/bb6/actions/runs/41966512900), **success**. Seven later t3/t4/t5/three-parent modules and Agent10's newest fourth-return modules have an independently queued source check [41969914856](https://github.com/FlareZ123/bb6/actions/runs/41969914856).

The new valuation-six, exact-four, and rooted-four modules are included in **queued** manual source run [41971162585](https://github.com/FlareZ123/bb6/actions/runs/41971162585), pinned to commit `a42b5c14397107ad7b70ca99464b1b048969e8ce`. Do **not** advertise these as unchanged-source-certified until the actual CI jobs succeed. Only the core t6 and the modular divisibility lemmas were locally checked against exact standalone stub definitions; the complete exact-four/rooted-four new files await actual source compilation. Any CI failure must be diagnosed, repaired, and rechecked.

Proof source:
- [FirstForkSix.lean](FirstForkSix.lean)
- [FirstForkSixResidues.lean](FirstForkSixResidues.lean)
- [FirstForkOddValuationSix.lean](FirstForkOddValuationSix.lean)
- [FirstForkExactFour.lean](FirstForkExactFour.lean)
- [FirstForkRootFour.lean](FirstForkRootFour.lean)

## Higher-value blank-root lead from inverse-cone computations

Independent exact-integer inverse enumeration using the source-compatible algorithm in Agent10's `reset_inverse_fast.py` found complete finite ancestral cone sample sizes `(n,nodes,min ancestor bit length)`: `(58,110,49)`, `(491,731,488)`, `(1024,1523,1018)`, `(2050,3099,2044)`, `(4096,6224,4089)`, `(8194,12459,8186)`. Because the reset graph is strictly increasing forwards, a completed backwards cone covers every possible reset root predecessor. Each sampled minimum is immense compared with root 2, but **no uniform lower bound is proved**. This observation suggests pursuing an all-index minimum-ancestor-bit-length bound on the fatal family, accounting for potentially arbitrarily high 3-adic odd branches.

The pure arithmetic single-even chain from fatal `c_n=4*2^n-(n+4)` has deficiency after j backwards even steps `D_j=(2^(j+1)-1)*n+3*2^j+1`, as long as the same even dyadic band persists. It offers a parametric starting point for a new **root-sensitive proof**. Empirical bit-length ratios and linear cone sizes cannot justify any extrapolated nonhalting claim. Agent10 was sent this line of inquiry at `communications/agent10/20261105T0453Z_agent7-fatal-cone-scale-lead.md`.

The actual original six-state #746 halting status and BB(6) remain unresolved.
