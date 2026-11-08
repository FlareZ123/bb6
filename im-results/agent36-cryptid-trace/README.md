# Cryptid D: original-source first sections and recursive zero-marker closure

**Research state: 8 November 2026.** New original-machine zero-marker packet theorems and a terminating depth-recursive safe language have been **kernel-certified** against the original six-state table in [manual Lean CI 42530949401](https://github.com/FlareZ123/bb6/actions/runs/42530949401). This is intermediate synthetic-section mathematics. The blank-root D machine remains undecided, so no exact BB(6) value or upper bound follows. [Earlier research log](FULL_RESEARCH_LOG.md).

## Section semantics and key theorem

The original machine is `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`. Use `I_n(s)` for state F scanning 0, with a physically blank left half-tape and right tape `1^n s`; all finite trailing zeros are physically immaterial. Define
- `M(a,q,p;Y)=I_a((01)^q 0 1^pY)`, the packet section;
- `Z_m=(01)^m0`, the **zero-ended marker**;
- `L(A,Q,B)=I_A((01)^Q1^B)`, the regular section language.

The [exact original-source theorem `e_zero_drop_Z`](EZeroZ.lean) proves, for **every** `k,q,m∈ℕ`,

```text
run(12k²+49k+50+4q, M(3k+4,q,0;Z_(m+1)))
    = M(8k+5,0,2q+7;Z_m).
```

This is literal configuration equality, preserving both machine state and every binary tape cell. It uses the unchanged `CryptidBoundary.full_E_pairs` original source lemma, with `Z_(m+1)=0 1 Z_m`.

## New unbounded regular-reentry families

The same [Lean file](EZeroZ.lean) composes that exact drop with Agent2's original-source packet normalization, B boundary, and A/p=0 code interpreter. The resulting **physically observable** `ObsEq` regular-return statements are:

| Input source | Quantification | Subsequent physical endpoint |
|---|---|---|
| `M(3k+4,q,0;Z_0)` | every `k,q` | **exact** `L(8k+5,1,2q+5)` at time `12k²+49k+50+4q` |
| `M(3k+4,3u,0;Z_(m+1))` | every `k,u,m` | some regular `L`, via `p=2(3u)+7≡1 mod3` |
| `M(9t+4,q,0;Z_(m+1))` | every `t,q,m` | some regular `L`, because the dropped packet is a B section with `q=0` |
| `M(9t+10,3u+1,0;Z_(m+1))` | every `t,u,m` | some regular `L`, because the dropped packet is an A section with `p≡0 mod3` |
| `M(27t+7,3u+1,0;Z_(m+1))` | every `t,u,m` | some regular `L` after one further exact guarded E packet step and an A/p=0 terminal |

These are mutually overlapping sufficient families, not a complete classification. Every result is universally parameterized and checks the *literal original machine* via physical tape equivalence. All have been audited by [CI 42530949401](https://github.com/FlareZ123/bb6/actions/runs/42530949401), with no `sorryAx` or native-decision dependence.

## A certified recursive sufficient criterion

The stronger reusable [`ZSafeNormalizer.lean`](ZSafeNormalizer.lean) imports the original-source guarded B/E packet normalizer. Define `d=normalizeWithCount(c).2` for a packet index `c=(a,q,p)` with `a≥4`. The terminal is immediately *safe* when

```text
d.p % 3 = 1
or (d.a % 3 = 0 and d.p % 3 = 0)
or (d.a % 3 = 2 and d.q = 0).
```

For a remaining `d.a % 3 = 1, d.p = 0` terminal, zero-marker depth zero closes by the exact first row above. At positive depth, the theorem replaces the index by `(8*((d.a-4)/3)+5, 0, 2*d.q+7)` and decreases the marker depth by one. The recursive predicate `safeZ m c` is finite by **structural recursion on the marker depth**, while the inner packet normalizer is finite by the already source-proved rank decrease `q+p↦q+p−1`. Its fully audited soundness statement is:

```text
safeZ m c  and  c.a ≥ 4
    => exists T,A,Q,B:
       run(T, M(c.a,c.q,c.p;Z_m)) ≈ L(A,Q,B).
```

The theorem `e_zero_safeZ` also specializes this procedure to `M(3k+4,q,0;Z_(m+1))`. The method composes **whole unbounded packet paths** with arbitrary-many zero-marker reductions, rather than proving a new short congruence case for every 3-adic arithmetic residue. The computed predicate is a *sufficient* original-source certificate. A rejected input is unresolved; the procedure is not a halting or nonreturn decision.

In particular, `p≡2 mod3` A/E terminal exits and some deeper E-reset chains remain possible. Agent2's active Z-marker A/p=2 work is complementary. None of these synthetic tapes is asserted to be reached by any authentic blank orbit.

## Earlier first-return work and rooted frontier

[AExtraBranches.lean](AExtraBranches.lean) proves explicit A extra-10 and A-E-pairs rules by specializing Agent35's mixed-word source theorem; original-source [CI 41474006959](https://github.com/FlareZ123/bb6/actions/runs/41474006959) passed. [ASixBoundary.lean](ASixBoundary.lean) adds the six-one A gate, [CI 41475009756](https://github.com/FlareZ123/bb6/actions/runs/41475009756). [EZeroFirstComplete.lean](EZeroFirstComplete.lean) and [EZeroFirstChain.lean](EZeroFirstChain.lean) handle strict physical first-return questions on exceptional E marker inputs. These are source-level statements about explicit input cylinders.

[trace_four_starts.py](trace_four_starts.py) projects 30,000 symbolic return steps from each of four named original blank prefixes and records reproducible digests. Its long projected compositions have no global original-source Lean theorem. The actual-root effort elsewhere in the repository has reached difficult finite exceptional reentries but lacks a universal invariant covering all reachable branches. See [the full log](FULL_RESEARCH_LOG.md) for scope qualifications and exact trace provenance.

**Highest-value next integration:** Apply `safeZ` to a source-certified *authentic blank-origin* packet section, and repair any reachable unsafe A/E p=2 tail by a new original-machine return theorem. A decisive result must establish either finite genuine halting or a globally closed nonhalting invariant, beyond the existence of these synthetic regular reentries.
