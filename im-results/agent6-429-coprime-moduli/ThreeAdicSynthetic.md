# Uniform all-3-adic synthetic halting theorem: Lean source audit

**Agent 6, 6 November 2026.** This is an integrated Lean-kernel proof for the complete repository BB429.next/run accelerator. It is a method obstruction, not a blank-root decision. The six-state Busy Beaver value remains unresolved.

## Main theorem

The module [ThreeAdicSynthetic.lean](ThreeAdicSynthetic.lean) proves:

~~~lean
Agent6ThreeAdic.synthetic_halt_every_three_power
  (E r : Nat) (hE : 1 ≤ E) :
  ∃ W n a b,
    W % 3^E = r % 3^E ∧
    BB429.run n (0,W) = some (a,b) ∧
    BB429.next (a,b) = none
~~~

Thus every residue cylinder of the second accelerated counter at exact first counter zero contains a finite halting trajectory of the complete twelve-branch source map. The starting point (0,W) is synthetic. No theorem here says it is reachable from the authentic blank start (0,0).

## Proof decomposition

Put M=3^(E-1) and reduce the target r to R=r % 3^E. Split on R % 3.

- **Class 0.** Agent 1's H0_all_residues supplies c≥2 with H0(c) ≡ R/3 (mod M). Agent 6's exact source-family identity is demand(c-2)=3*H0(c); Agent6TwoBurstZero.full_source_synthetic_halt certifies the corresponding complete-source-map trajectory.
- **Class 1.** The source demand satisfies demand(q-1)+29=24*G1(q). The parameter q is chosen even, q=2n. This is the useful scaling trick: F(n)=8*G1(2n) obeys the generic lift identity F(n+2*3^e)+2*3^e ≡ F(n) (mod 3^(e+1)). Agent 1's generic all_residues theorem therefore covers every residue for this scaled sequence. The source trajectory is supplied by Agent6TwoBurstOne.full_source_synthetic_halt(q-1).
- **Class 2.** Agent 1's G2_all_residues supplies t≥1 with G2(t) ≡ R/3+5 (mod M). The initial counter is 3*G2(t)-13. The exact first-burst gateway identity gives the source halting prefix, and BB429DyadicStarts.first_prefix_is_source transfers it to the full BB429.run map.

The shared transport lemma proves that equality modulo M lifts through multiplication by three modulo 3M. The offsets 13 and 29 are canceled with the source-certified modular cancellation lemma. All natural-subtraction bounds are discharged in Lean.

## Methodological corollary

The same module proves Agent6ThreeAdic.no_three_power_periodic_invariant. For every fixed E≥1, there is no predicate P on accelerated states satisfying all four properties:

1. P (0,0);
2. saturation at exact first counter zero: if x % 3^E = y % 3^E and P (0,x), then P (0,y);
3. forward invariance under every successful BB429.next transition;
4. exclusion of every halting state.

The proof takes the synthetic halting start in the residue class of zero, transfers P from blank by saturation, propagates it along the finite source run, and contradicts the halt-exclusion condition. This rules out a broad fixed-3^E two-counter invariant strategy. It leaves history-sensitive and genuine-root reachability arguments available.

## Verification

**Unchanged-repository source CI passed:** [GitHub Actions run 42299330210](https://github.com/FlareZ123/bb6/actions/runs/42299330210), commit 0c60da7ec7d404f86af62872fb7b8ac7fb035d40, Lean **4.36.0-rc2**. The manual-only workflow is [agent6-429-threeadic-synthetic.yml](../../.github/workflows/agent6-429-threeadic-synthetic.yml). It compiles the unchanged BB429Rank, BB429Burst, BB429DyadicStarts, both Agent 6 two-burst source families, and Agent 1's three arithmetic modules before compiling the integration theorem.

The final log reports:

~~~text
'Agent6ThreeAdic.synthetic_halt_every_three_power'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'Agent6ThreeAdic.no_three_power_periodic_invariant'
  depends on axioms: [propext, Classical.choice, Quot.sound]
~~~

There is no sorryAx, custom axiom, native_decide, or copied transition function in either final theorem. The dependency modules' audits likewise show only ordinary Lean axioms.

## Scope and open obligations

- The result concerns the exact repository accelerator BB429.next/run; this workflow does not independently re-import the pinned upstream raw Cryptids Turing-machine source.
- The synthetic starting counters are not shown reachable from (0,0). No #429 halt/nonhalt decision follows.
- The theorem concerns powers of three and fixed first counter zero. The broader all-moduli synthetic theorem in the adjacent dossier remains a separate paper-level result.
- This does not establish a global six-state coverage certificate, an exact BB(6) upper bound, or an attained BB(6) lower bound.

The result is retained in im-results/ because it closes a formalization and method-obstruction gap while leaving the actual BB(6) objective untouched.
