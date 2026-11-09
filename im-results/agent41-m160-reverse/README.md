# Machine C: a mixed-factor 160-modulus all-time inverse obstruction

## Exact claim and scope

For the original Machine C accelerated transition system `BB6CLine.nextC` starting from `(5,0,1)`, the new Lean theorem is:

```lean
Agent41M160.source_no_45_63 (a k : Nat)
    (ha : a % 160 = 45) (hk : k % 160 = 63)
    (h : BB6CLine.Reach (a,k,0)) : False
```

Thus every state in the infinite `(45 mod 160, 63 mod 160, c=0)` rectangle is absent from the genuine blank-origin counter orbit. The stopping-parameter corollary, `source_no_second_stop_family_160`, eliminates every authentic second-stopping candidate satisfying

```text
j % 160 = 21,   m % 160 = 45,
k + j + 3*m + 5 = 2^(2*m+2) * (j+3)
```

because then `(2*j+3)%160=45` and `k%160=63`. There are infinitely many nonnegative parameter pairs in the indicated progression, with a nonnegative `k` supplied by the equation for sufficiently large parameters. This is **one necessary halting-input family exclusion**, not a decision of Machine C, a solution of BB(6), or a proof of external novelty. All other stopping families and the unbounded parameter existential remain unresolved.

**Verification boundary:** the complete seven-module proof compiled locally with Lean **4.36.0-rc2**, against a local `CLine.lean` containing exactly the repository's `nextC` and `Reach` definitions. The final axiom audit was `[propext, Classical.choice, Quot.sound]` (no `sorryAx`). An independent GitHub Actions workflow now rebuilds against the **unchanged full original** `im-results/agent11-c-line/CLine.lean`; until that workflow succeeds, describe the source audit as *locally source-definition checked*, rather than an original-file CI certificate.

## Mathematical mechanism

Let `d=(a+160-c%160)%160`, `t=(a+k)%160`, and `u=(t+40*(d/80))%80`. For `c>=8`, the reverse bad-state predicate is the union of exactly seven modular clauses:

```text
(d%80,u) = (23,10), (24,11), (49,25), (63,30), or (64,31)
or (d=97 and t%80=51)
or (d=42 and t=105).
```

For `c<8`, exclude `c=2` and set `s=0` for `c<4`, otherwise `s=c-3`; let `x=(a+160-s)%160`, `w=(k+c)%160`. The low reverse predicate requires one of

```text
x=26, w%80=67;   x=45, w=63;       x=52, w%80=56;
x=66, w%80=47;   x=106, w%80=27;   x=132, w%80=16;
x=146, w%80=7
```

together with `k>=8` or the unique permitted small-right exception `(x,w)=(146,7)`. The source root `(5,0,1)` violates this predicate; all `(45 mod 160,63 mod 160,0)` targets satisfy it.

The Lean core proves **backward closure** of this entire predicate for each original `nextC` branch, including the low-phase edge `c=8→7` and both zero-left high-phase branches. Two finite `Fin 160` checks are ordinary kernel-reduced `decide` propositions; all unbounded lifted steps are proved by modular arithmetic in Lean. Induction over the actual `BB6CLine.Reach` constructor excludes the target for **all time**, without a simulation bound. The odd-`m` stopping corollary uses `2^(2*m+2)%160=96`, since `m>=3` and odd.

## Experimental discovery and novelty boundary

The auxiliary `B=8,M=160` finite quotient overapproximates every original `nextC` step by taking representatives `x` and `x+160` for high classes. A local C++ BFS reached **2,427,090 / 4,741,632** abstract states, examining **18,173,786** representative transitions. Reverse traversal from quotient target `(45,63,0)` produced a **4,046-state** forced predecessor basin, compressed into the clauses above. The proof itself uses the exact source transitions, not the BFS counts.

Independent finite screens with `B=8,M=384` and `B=8,M=512` admit the stopping-family example `j=21,m=8525`, whereas M160 excludes it. This establishes *finite quotient nonredundancy* only. Other global source theorems and section-return sieves might already exclude the family, so source-theorem novelty relative to the entire repository is not yet established.

## Reproducibility and continuation

The exact seven Lean files `M160Defs.lean`, `M160Finite.lean`, `M160Low.lean`, `M160Gateway.lean`, `M160Zero.lean`, `M160Source.lean`, and `M160Stopping.lean` are preserved in [M160Proof.tar.xz.b64](M160Proof.tar.xz.b64), a Base64-encoded xz tar archive. **Archive SHA-256:** `1e7d71f11c70b4fedca6fe9040a2bd389b5e7cdbeb137c90a420e1c8af99e81c`. Unpack the base64 archive and compile the seven files in that order with `LEAN_PATH=.`, after compiling `CLine.lean` from `im-results/agent11-c-line/`. A manual-only CI workflow, `.github/workflows/agent41-m160-source-check.yml`, executes exactly this compilation against the original full file and audits the named theorems.

The next useful investigation is to compare this rectangle against the source-exact [joint low/high stopping criterion](../agent19-c-odd-dyadic/JointCriterionIntegration.md) and [source-first-return equivalence](../agent15-c-halting/SectionReachEquivalence.lean). If the mixed-factor approach supplies genuinely new surviving families, generalize the compact inverse template to other odd factors, without conflating finite-quotient admission with authentic root reachability.
