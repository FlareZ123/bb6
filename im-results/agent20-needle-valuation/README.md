# Space Needle: sharp incoming-terminal valuation bound and unique equality

**Agent 20, 2026-11-04. Intermediate original-high-level arithmetic research; not a BB(6) decision or a new machine classification.**

## Statement

The pinned Google DeepMind Cryptids six-state Space Needle high-level map is
`highLevelNext` on `N d`, with original blank entry `N 1`. Agent48's
source-checked `SpaceNeedleClosed.lean` proves the complete predecessor identity.
A nonterminal predecessor with the exact factorization

```text
d+2 = 2^v (2q+3)
```

enters the terminal target with `d'+2=2^K` precisely when

```text
2^K = 2^v (2q+3) + v + 3(q+1).           (1)
```

Here `v,q,K` are **all arbitrary natural numbers**, and a legal incoming
edge is completely different from blank-root reachability.

The new, independent all-natural Lean theorem `NeedleGap.gap_all` proves:

```text
Equation (1)  =>  2v+1 <= K.
```

The bound is **sharp** and has a unique equality case:

```text
Equation (1) and K=2v+1  <=>  v=6, q=61, K=13.
```

The forward implication is the Lean theorem `gap_equality_unique`.
The reverse direction is exactly `2^13 = 2^6*(2*61+3)+6+3*(61+1)=8192`.
Consequently `gap_strict_except_unique` proves `K >= 2v+2` for
every legal predecessor except the pair `(v,q)=(6,61)`.

For the actual original-source terminal tower `haltTower k`,
the source bridge `A20SourceBridge.lean` states:

- `terminal_incoming_valuation_bound`: `2v <= k`;
- `terminal_boundary_unique`: equality `k=2v` forces `v=6,q=61,k=12`;
- `terminal_incoming_strict`: all other incoming edges have `2v<k`.

These quantify over *every legal immediate incoming high-level edge*, not merely
sampled exponents, and give a finite valuation search ceiling for each fixed
terminal exponent.

## Proof mechanism

Write `B=2^v`. To prove the lower bound for `v>=5`, suppose `K<=2v`.
The equality and `2^K<=2^(2v)` imply `q<2^(v-1)`. Since
`v+3<=2^(v-2)`, the positive remainder `3q+v+3` is less than `2B`.
Dividing the equation `2^K=B(2q+3)+(3q+v+3)` by `B`, the quotient
`2^(K-v)` is even, while `2q+3` is odd. The exact interval
`2q+3<2^(K-v)<2q+5` forces
`2^(K-v)=2q+4` and `3q+v+3=B`. Combining these gives
`3*2^(K-v)+2v = 2^(v+1)+6`, contradicting `K-v<=v` and
`v+3<=2^(v-2)`. The `v=0,1,2,3,4` cases are directly exhausted by
the same exact Diophantine equation.

For unique equality, substitute `K=2v+1` into equation (1) and rearrange,
where `B=2^v`, `D=2B+3`:

```text
D*(q+3)+v = D*B+6.
```

For a valid equality, the small cases `v<2` are impossible; for
`v>=2`, both `v` and 6 are strictly below `D`, so taking residues
modulo `D` yields `v=6`. Substituting back forces `q=61`.
The Lean proof uses natural-number identities and kernel-checked modular
reasoning, with no unproved primality or external arithmetic oracle.

## Verification and trust

- `A20NeedleGap.lean`: **locally compiled with Lean 4.36.0-rc2**, no
  `sorry` or custom axiom. The final theorem's printed axioms are exactly
  `[propext, Classical.choice, Quot.sound]`.
- `A20UniqueBoundary.lean`: **locally compiled** against the preceding
  module, only standard axioms. No `sorry` or local axiom.
- `A20SourceBridge.lean`: locally compiled against a signature-matching
  *stub* for Agent48's already proved source lemma; the local axiom output
  includes this original-lemma placeholder. The authoritative original-source
  audit is the dispatch-only
  [GitHub workflow](../../.github/workflows/agent20-needle-valuation.yml),
  importing unchanged Agent48 source and pinned upstream Cryptids commit
  `ced8f9f44f67a167d5ecc03e687b048c67926371`.
- **Full original-source CI [41765478125](https://github.com/FlareZ123/bb6/actions/runs/41765478125) SUCCEEDED** on the exact checked-in original Cryptids source, including source recompilation, all three new source theorems, and `#print axioms` of every theorem: only `[propext, Classical.choice, Quot.sound]`. A separate independent Lean 4.36 arithmetic job also succeeded on the committed sources. The older runs [41764201552](https://github.com/FlareZ123/bb6/actions/runs/41764201552) and [41764927601](https://github.com/FlareZ123/bb6/actions/runs/41764927601) failed **before source compilation** because exhaustive Mathlib cache extraction exceeded runner storage; a selective transitive cache download resolved the infrastructure issue.

Closest repository prior work: Agent48's
[Space Needle source dossier](../agent48-space-needle/README.md)
and Agent20's
[all-exponent residue predecessor results](../agent20-needle-coprime/README.md).
Neither earlier note states this sharp **valuation-versus-terminal-exponent**
inequality or the unique equality witness, as far as the surveyed material
shows. External mathematical novelty has not been independently checked.

## Critical limitation and next work

The bound eliminates large valuations `v` from a **single fixed terminal
predecessor** search. It does not restrict the historical blank-start
counter sequence sufficiently to prove that its actual orbit avoids
the remaining predecessors. There is no new universally valid BB(6) upper
bound, no proven Space Needle halting/nonhalting classification, and no claim
that this known holdout is resolved. A useful next step would combine the
all-source valuation ceiling with an authentic blank-reachable valuation
invariant, or derive deeper multi-step predecessor restrictions.

## Stronger asymptotic result

The companion [SUPERLINEAR.md](SUPERLINEAR.md) now gives a fully written elementary proof that for every fixed positive integer `c`, any legal incoming edge with `v>=4*(3^c+1)` must have terminal exponent `K>c*v`. Hence the terminal exponent grows faster than every fixed multiple of the input valuation, and asymptotically `K=Omega(v log v)` along the unrestricted predecessor set as `v→∞`. This result is a **hand mathematical proof, not a Lean theorem** yet; the finite modular cross-check reports zero counterexamples among 965,856 eligible `(v,K)` pairs. It does not imply anything about actual blank-start reachability.
