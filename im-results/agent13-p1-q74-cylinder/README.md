# P1: a new q=74 affine critical-gateway cylinder

**Research status (6 November 2026): successful original-source Lean 4.36.0-rc2 proof of an all-time P1 blank-root exclusion for one new infinite critical-index cylinder.** The exact full import chain and final theorem compiled in [successful CI 42310575677](https://github.com/FlareZ123/bb6/actions/runs/42310575677) at commit `db50f17cd337191501973605254d715261af418f`. The proof uses only Lean standard axioms and no `sorryAx`. It does not decide P1 halting or BB(6).

## Claim and source boundary

For the source P1 machine `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`, let `H(n)=14*2^n-2*n-10`. Define `q=74+2^18*r`, so `n=16*q+2=1186+2^22*r`. [Q74Final.lean](Q74Final.lean) states

```lean
theorem critical_1186_mod_4194304_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(74+P*r)+2)-2*(16*(74+P*r)+2)-10)
```

where `P=262144`. A correct proof rules out **every** genuine blank-start visit to the necessary halting gateway for the entire infinite critical-index progression. It neither proves that every other gateway is unreachable nor supplies a global six-state Busy Beaver upper bound. The original Turing-machine-to-accelerated-map bridge is external to these two files, via the pre-existing DeepMind/Agent1 formalization.

## Exact inverse-graph certificate

Following the unchanged original P1 feeder reduction, use the two scalar shadow roots `(0,12q+4)` and `(0,10q+4)`. A shadow node `(m,z)` has a possible inverse successor `(m+t+1,z')` exactly when

```text
z = 2^t * v,       2*z' + 1 = 16*q + side + m + t + v
```

with `side=8` or `side=9`, respectively. We exhibit *all* affine nodes `(m,a,b,k)`, meaning `z=a+b*r`, `k=1+v₂(a)`, and `2^k | b`. The two closed lists in [Q74Nodes.lean](Q74Nodes.lean) have **25 and 29 nodes**. They have maximum inverse cost **18**, and maximum `k=6`. In particular they satisfy the original theorem's uniform `m≤41` and `1024∤z` prerequisites.

The exact positive-cost affine successor is

```text
(m,a,b,k) → (m+t+1, (16*74+side+m+t+a/2^t)/2, 8*P+b/2^(t+1), k')
```

whenever the base numerator is odd and `0≤t<k`; the bound `2^k | b` proves these are all possible successors for every `r≥0`. At each target the `k'` is recomputed from its base coordinate. `Q74Nodes.check0` and `check1` assert that the original Agent9 adaptive Boolean checker accepts both explicit finite lists. [Q74Final.lean](Q74Final.lean) transports these checks to arbitrary `r` using the original `BB6.Agent9Adaptive.check_sound` and `check_bounds`, then applies the unchanged source theorem `BB6.Agent9Generic41K.critical_unreachable_of_shadow41K`.

This `2^18` cylinder is sharper than the generic `2^(B+K)` conservative period, which would give `2^24` for `B=18,K=6`. The smaller period is a **computed finite affine closure**, with no extrapolation from finite simulation.

## Evidence and reproduction

- The two graphs were exhaustively generated from the exact scalar successor equation. Independent complete graph enumerations of `q=74+262144*r` at `r=0,1,2,5,17,1000` agree exactly with the projected 25/29-node affine lists. This is finite corroboration, not the all-parameter theorem.
- A local Lean 4.36.0-rc2 source-identical Boolean checker independently compiled `checked0` and `checked1` using `by decide`, with axioms `[propext, Classical.choice, Quot.sound]` and no `sorryAx`. This did not compile the entire original-source proof.
- A dedicated manual-only workflow [agent13-p1-q74-source.yml](../../.github/workflows/agent13-p1-q74-source.yml) compiles the unchanged original P1/Agent9 imports, the complete affine checker, and the final true-root theorem with an axiom audit. **Successful full source audit:** [42310575677](https://github.com/FlareZ123/bb6/actions/runs/42310575677), source commit `db50f17cd337191501973605254d715261af418f`. Both original-source modules and the final `#print axioms` declaration passed in the manual-only workflow.

## Comparison and unresolved question

The q-residue 74 lies outside Agent9's earlier source-certified 700/1024 density sieve and its twenty new q mod4096 shallow classes. It also differs from the explicitly source-certified q37,41,53,65,70,89 cylinders. This establishes a previously unrecorded repository infinite-cylinder exclusion now certified against unchanged original source; external originality has not been evaluated.

The actual research bottleneck remains untouched: the P1 blank-entry orbit must be separated from **every surviving** critical parameter, including gateway residue classes outside all currently proved cylinders. The finite affine certificate does not construct a global invariant ruling out that entire infinite union. Prefer parameter-uniform closure of remaining exits or a genuine halting witness over extending an unbounded list of isolated residues.
