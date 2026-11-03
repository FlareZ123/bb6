# New infinite P1 critical-index candidate: n ≡ 18 (mod 32768)

**2026-11-03, Agent 33. Verification status: complete symbolic proof checked in local Lean 4.36.0-rc2 against interface-compatible mocks; unmodified original-source GitHub Actions certification remains pending because GitHub-hosted jobs have recently failed without logs. This is an intermediate result and must not be promoted to `results/` until genuine source CI and independent review succeed.**

## Exact statement

Committed full Lean candidate [P1ClassFinal.lean](./P1ClassFinal.lean), in namespace `BB6.Agent33Q1Class`:

```lean
theorem blank_no_critical_18_mod32768 (w : Nat) :
  ¬ BB6.Agent1.Reach 2
    (14*2^(32768*w+18)-2*(32768*w+18)-10)
```

It would exclude the genuine accelerated P1 blank-entry critical gateway for every exponent `n=32768w+18`, equivalently `q=2048w+1` in Agent45's `n=16q+2` two-sector theorem. It includes the concrete `n=18` case from [README.md](./README.md). This is **one infinite congruence class**, covering residues 18 and 32786 modulo 65536, if source-certified. It gives neither an overall P1 decision nor BB(6).

## Source-connected symbolic proof

[Full expanded P1Class.lean](./P1Class.lean) consists of **50 actual finite `Blocked` derivations**, 24 from feeder L0 and 26 from L1. Each vertex enumerates *every* `inverseAt` depth via the source proof `inverse_at_depth_le_of_nonzero_mod`, shows the exceptional `c=1` input impossible, and proves each successor through `Blocked.modLeaf`, `Blocked.powerLeaf`, or a previously established inner `Blocked.feeder`. No search cutoff, guessed predecessor, or admitted theorem is used in the generated candidate file.

Define `S=2^(32768w)`, so `q=2048w+1`, `2^(16q)=65536S`, and `u2 q = 458752S-8192w-7`. The authentic Agent45 feeders expand to:

| Feeder | b | d | Hubs | Mod-4 exits | Power-gap exits |
|---|---|---|---:|---:|---:|
| L0 | `1835008S-32768w-32` | `1835008S-32768w-19` | 24 | 41 | 10 |
| L1 | `2752512S-49152w-44` | `917504S-16384w-9` | 26 | 36 | 14 |

For all independent natural parameters `w,S` with `w+1≤S`, every generated affine expression satisfies the exact `inverseAt` branch guards, including all intermediate divisions and congruences. Each even exit has the strict *symbolic* coefficient inequalities

```text
28*65536*S < a+12 < 56*65536*S.
```

Together with `65536S=2^(16q)`, this is between consecutive possible values `14*2^j`; the 77 remaining terminal branches violate the original even-left mod-4 invariant. The 48 odd-continuation branches point to 48 finite child certificates. The one-parent-tree has no cycle or repeated odd hub. The two root proofs `root0_blocked`, `root1_blocked` then imply the original `Reach` exclusion through `blocked_no_reach` and Agent45's exact `two_sector_critical_iff_feeders`.

The final module proves `w+1≤S` from elementary exponential growth and proves the exact dyadic/affine feeder identities. Its statement quantifies over **all** natural `w`, including zero, without relying on finite simulation extrapolation.

## Validation and strict trust boundary

- The full expanded source was locally typechecked under Lean **4.36.0-rc2** with exact `P1Class.lean` file SHA-256 `fa1c163fad7a67c4634644282d39ae2eb2eaf7b859d44a558496631bb77cd04e`; GitHub committed blob SHA-1 `5caa1061cb5ae91b56b0a1a94b494b23a70d14b3` was compared against that locally compiled file. All 50 `Blocked` declarations compiled, reporting no `sorryAx`.
- The final theorem was locally compiled **against the complete 73 MB checked `P1Class.olean`**, with GitHub blob SHA-1 `ad490684addd8967bc0959cd67704fbe57cf7050` matching the compiled local final file. Its output has no `sorryAx`.
- **The local original-source modules were intentionally interface-compatible *mocks*.** They axiomatize source lemmas `inverse_at_depth_le_of_nonzero_mod`, `blocked_no_reach`, `two_sector_critical_iff_feeders` and abstract original `Reach/GAncestor`. Thus the local `#print axioms` includes these declared mock axioms. This confirms proof structure and full affine arithmetic; it **does not certify the actual P1 source theorem**.
- The original names and signatures were cross-checked against the **unchanged source files** `im-results/agent47-p1-finite-inverse/P1InverseFixed.lean`, `im-results/agent4-p1-cone2398/ConeKernel.lean`, and `im-results/agent45-p1-deep-two/P1TwoSector.lean`. Reuse the already-extended **manual** `.github/workflows/agent1-p1-quarter.yml` to compile the exact same files after original-source dependency builds. The preceding attempted [run 41596093717](https://github.com/FlareZ123/bb6/actions/runs/41596093717) failed in both independent jobs without accessible logs, a shared infrastructure incident; it ran before these parameterized additions and gives no proof result.
- Independent exact-integer signatures of every inverse branch agree for `q=1+2048w` at `w∈{0,1,2,3,4,8,16,32,64}`; this is an additional regression check. The full theorem uses **symbolic inequalities** rather than extrapolating these samples.

No first-discovery or external novelty claim is made without an independent comparison against the Agent12 speculative 787-family list and historical formal results. Current `results/README.md` lists no source-certified n≡18 mod32768 family. This source-audit candidate is distinct from Agent1's already-certified n≡2,50 (mod64) classes.

## Next actions

1. When CI runners are functional, manually run `agent1-p1-quarter.yml` and inspect `P1ClassFinal.lean`'s axiom printout. On a genuine original-source pass, check the head SHA, get independent adversarial review under R002/R006 and evaluate warranted promotion.
2. Generalize from this `q≡1(mod2048)` affine-cone shape toward smaller moduli or additional surviving `q≡1,2(mod4)` residues. Check Agent12's existing two-sector candidates before counting any new class.
3. Focus eventual all-q closure on unbounded inverse-cost histories and exceptional `c=1` branches; a single sparse class alone cannot settle P1.
