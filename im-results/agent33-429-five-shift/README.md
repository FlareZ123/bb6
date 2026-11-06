# Machine #429: five complete shifted terminal cylinders from the genuine blank root

**Intermediate mathematical result, 6 November 2026. BB(6) remains unresolved.** The proposed theorem excludes five infinite terminal families of one authentic blank-start accelerated six-state machine, using a small-quotient rank straddle and a source-proved parametric inverse kernel. This work does not decide #429, give a global BB(6) upper bound, or exhibit a new halting machine.

## Exact statement

For the existing verified accelerator `BB429.next` in [BB429Rank.lean](../agent5-429-rank/BB429Rank.lean), let `BB429.run n (0,0) = some (a,b)` denote the genuine blank-root section. Its exact terminal line is `b+1=2*a`. The new proof module [BB429FiveShift.lean](BB429FiveShift.lean) states, for **every** natural time `n` and terminal `(a,b)`:

```lean
a % 16384 ∉ [1233,5117,7165,8189,14333]
```

Equivalently, none of the infinite affine rays

```
(a,b) = (16384*q+r, 32768*q+2*r-1)
r ∈ {1233,5117,7165,8189,14333}, q ∈ ℕ
```

is genuinely blank-reachable. This exact statement is asserted by `BB429FiveShift.blank_halt_not_five` and `no_reach_five`. The 5 residues are distinct from Agent 30's 40 newly proved modulo-16384 rays and the earlier 11473 ray. The current 52/8192 necessary mask has 104 lifts mod16384; after Agent30's 41 and these 5, the combined arithmetic mask has **58** remaining necessary residue classes modulo 16384. That count is conditional on the referenced original-source evidence and does not imply reachability for any survivor.

## Proof mechanism

Agent 33's earlier [parameter-uniform inverse kernel](../agent33-429-24/BB429InverseKernel.lean) and Agent 30's [stronger positive-even/root-exception kernel](../agent30-429-even16/BB429InverseKernel16.lean) provide `cert_sound`: a checked finite inverse tree for an affine family `(A*q+a,B*q+b)` proves nonreachability for **all q**. The earlier [Agent 1 four-cylinder proof](../agent1-429-four-split/BB429FourSplit.lean) established the complementary **rank-straddle** technique for handling small concrete seeds; this contribution reuses that idea and Agent30's kernel for five additional, previously surviving rays.

At shift `q≥1`, kernel depth 12 closes residues 1233, 5117, 7165, and 14333. Residue 8189 needs `q≥2` before its inverse tree closes. These checks are **symbolic all-parameter certificates**; no finite collection of sampled values of q is substituted for the universal proof.

Small-quotient endpoints are eliminated using the authentic `run` and strict rank increase. If the true trace crosses a target's rank between consecutive steps `k,k+1` without landing on that target, then no earlier or later step can equal the target. The exact checkpoints and targets are:

| Terminal first counter a | q | Crossing step k | State at k | State at k+1 |
| ---: | ---: | ---: | --- | --- |
| 1233 | 0 | 1056 | (189,4552) | (381,4171) |
| 5117 | 0 | 4754 | (25,20417) | (53,20364) |
| 7165 | 0 | 6602 | (3069,22520) | (6141,16379) |
| 8189 | 0 | 7623 | (14333,4080) | (0,32756) |
| 14333 | 0 | 13916 | (24573,8185) | (20484,16370) |
| 24573 | 1 (8189 ray) | 23570 | (117,98057) | (237,97820) |

The `BB429FiveShift.lean` source avoids a massive single reduction by verifying the genuine source run in checkpoint blocks of 200 accelerated transitions. Each block is separately closed by `by decide` over the unchanged `BB429.run`; `BB429.run_add` composes them, and the original rigorous rank bounds rule out all alternative times. This is an exact finite computation certificate composed with an unbounded mathematical theorem. It is **not** merely empirical finite simulation.

## Evidence and provenance

- The original repository Lean4.36 source is the unchanged [BB429Rank.lean](../agent5-429-rank/BB429Rank.lean) from Agent5 plus previously source-audited inverse dependencies from Agents 6, 39, and 30.
- The six rank checkpoint pairs were cross-checked by a second local Python implementation of the 12-branch transition map and independently compiled locally in Lean 4.36.0-rc2 using the exact copied transition definition, run combinator and 200-step certificates. These local checks alone do **not** establish that the new module typechecks against the unchanged repository imports.
- The full unchanged-repository-source verification is the manual-only [CI workflow](../../.github/workflows/agent33-429-five-shift.yml), launched as [run 42294269373](https://github.com/FlareZ123/bb6/actions/runs/42294269373). **Until that run succeeds, classify the full five-family theorem as pending source-linked certification.**
- A separate pinned, unchanged upstream Google DeepMind Cryptids raw-Turing-machine bridge has not yet been executed for this exact five-family composition. The existing bridge from the original machine to `BB429.run` is established by prior project formalizations, and this file relies on it rather than independently reopening that semantic proof.
- The existing split+rank method and kernel theorem are credited to their authors. The new computation consists of the five enumerated rays and their authenticated, parameter-uniform combination after successful CI.

## Remaining obligation

The combined necessary mask still has **58 infinite families**. More modulus lifting and finite rank straddles do not establish nonhalting until every terminal from the authentic blank orbit has been excluded. Prioritize history-sensitive, globally closed root invariants or a finite certified maximality argument; quantify any future claims against the exact original blank root. This dossier belongs in `im-results/`, not `results/`, unless later work demonstrates independent academic novelty beyond adjacent proof techniques.
