# Critical P1 right-five gate as a guarded first return

**Mathematical claim.** For every n≥14 put Q=7·2^n−n−3. An original-source odd inverse history from (14·2^n−2n−16,3) to any (b,5) exists exactly when some q≥5 and k>0 satisfy q+k=Q, the moving-modulus recurrence r_0=1, r_j=2r_(j−1) mod (q+j) has its first positive return to 1 at j=k, and each wrap satisfies r_j+8≤q+j. This reduces the right-five gate itself, not blank-start reachability of every P1 terminal or BB(6).

**Proof status.** Original-source equivalence passed the exact dependency-closure Lean 4.36.0-rc2 workflow at commit 62e88e75ccf52af7c3fd872d32e3168c7a6f745b ([run 45508108201](https://github.com/FlareZ123/bb6/actions/runs/45508108201)). The near-2n cost bound passed the exact original-source dependency closure with strict standard-axiom checks at commit ca1fe6517197faede9ccf45080b82898adb7fc23 ([run 45508888563](https://github.com/FlareZ123/bb6/actions/runs/45508888563)). The general superlinear result below is a paper theorem. The explicit three-block bound now has a complete integer-only Lean recurrence proof checked locally; the original-source adapter and full dependency workflow are queued for verification.

## Exact scalar and source equivalence

Write v=(d−1)/2. For root b0+10=2Q, every inverse history has b+2v+2m+8=2Q at cost m. A legal forward gap of length k has p+(Q−m)=2^k v', parent p+8+m≤Q, child v'≥2 and v'+4+m+k≤Q. These are exactly the Gap constructors.

Forward transport uses the original inverseAt_iff_power_mass and odd_cone_mass lemmas, with v'=(c+3)/2 and k=t+1. Conversely, given a legal gap, set t=k−1, c=2v'−3 and s=Q−(m+k)−v'−2. The size guards give b≥8 and s≥2. Because k>0, the dyadic equation makes Q−m+p even, so the parent mass forces b≡0 mod 4. Direct substitution gives both exact inverseAt equations, including 2s+c+2t+1+c%2=b+d. The source constructor therefore yields (2s−4,c+4) at cost m+k. This includes the exceptional c=1 edge when v'=2. There is no extraneous prepared-state parity assumption.

The scalar right_five_iff theorem equates existence of Gap Q m 2 with the stated first-return criterion. The first step is 1→2; subsequent reverse gaps consume zero bits followed by one wrap. The final 1 must occur at a wrap by parity. Guarded-prefix decomposition and the interior lower bound recover a full legal path. In particular zero is absorbing, and an earlier return to 1 cannot be skipped.

## Uniform near-2n cost floor

For every n≥14 and original OddCone from (14·2^n−2n−16,3) to (b,5) at cost m, the exact return length is k=m+1. [ShadowCost.lean](ShadowCost.lean) and [CostSource.lean](CostSource.lean) establish the stronger necessary inequality

    2^max(0,m−n−1) · (m+1) > 2^n,

hence

    m > 2n − floor(log₂(2n−1)).

This improves the earlier 1.5n+O(1) uniform floor for large n without a reset-count hypothesis. For instance n=10002 requires m>19990. The proof starts from P=2^n. For a proposed return with 2^max(0,k−n−2)·k≤P, the first n+2 steps double exactly. If k exceeds n+2, step n+3 gives P+k at modulus 7P−k. From there the ideal cycle is P,2P,4P; after s steps the actual value lies between its ideal phase and that phase plus (2^(s+1)−1)k. The error bound is sufficient to preserve each wrap decision up to the proposed terminal time. Every terminal residue in this regime is ≥P, contradicting return to 1. The proof even excludes unguarded returns in that range. The remaining challenge is an upper bound on feasible history costs or an exclusion of the longer return lengths.

## Superlinear cost floor (paper proof)

[RenewalCost.md](RenewalCost.md) strengthens the floor further: for every fixed integer B≥1, for all sufficiently large n every original right-five history satisfies m>(B+1)n+2. The threshold is effective. In particular the explicit three-block proof gives m>4n+2 for EVERY n≥8000, including all currently unresolved critical indices n≥10002. The first return lands near phase 1/7; the exact renewal adapted from Agent50's rational block lemma has successive phase denominator 7-valuations 1,3,5,7,..., so no phase can vanish. Uniform error and clock bounds prove safety of any fixed number of n-step blocks as n grows. Exact constants and independent trajectory regressions are in [renewal_check.py](renewal_check.py). This is a paper theorem with a source-checked return adapter; it does not exclude superlinear costs or settle P1.

## Finite integer renewal formalization

The rational series in the paper proof can be eliminated. Write M=2^L−1 for a period of doubling modulo odd D, and h(p)=Σ_(0≤j<L) 2^(L−j) (2^j p mod D). The exact finite identities h(2p mod D)+2Mp=2h(p) and h(p)≡Lp (mod D) control the early matched wraps and the next phase numerator. The late block uses an integer lattice gap, so no assumptions on the later wrap word are needed.

- [RenewalCore.lean](RenewalCore.lean), [RenewalShadow.lean](RenewalShadow.lean), [RenewalLate.lean](RenewalLate.lean): finite periodic phase, early exact invariant, late error and grid separation.
- [RenewalBlock.lean](RenewalBlock.lean): generic renewal and nonzero normalized next phase.
- [RenewalNumeric.lean](RenewalNumeric.lean), [RenewalScales.lean](RenewalScales.lean): explicit denominator certificates and dyadic margins for every n≥8000.
- [RenewalFourN.lean](RenewalFourN.lean): composition of the three blocks, no return for 0<k≤4n+3.
- [RenewalSource.lean](RenewalSource.lean): original OddCone cost floor m>4n+2. Full source closure pending.

The local exact recurrence proofs use Lean 4.36.0-rc2 and only standard axioms. The general B result still relies on the paper denominator-growth argument.

## Remaining mathematical target

The recurrence is the Borwein–Loring recursion a_(t+1)=2(a_t mod t), with a_(q+j+1)=2r_j. See Borwein and Loring, *Some Questions of Erdős and Graham on Numbers of the Form sum g_n/2^g_n* (1990), and Dearden and Metzger, *Running Modulus Recursions* (2010), https://cs.uwaterloo.ca/journals/JIS/VOL13/Dearden/dearden3.pdf. Eventual hitting of zero is conjectural generally and would not preclude earlier safe return to 1. Agent 3 previously identified this family for F118. The useful P1-specific target is now the absence (or exact construction) of guarded first returns at clocks Q=7·2^n−n−3 on the critical n classes, and its connection to the remaining blank-root exit cases.

## Reproduction

Use the existing workflow `.github/workflows/agent9-p1-shadow-depth.yml`, selecting `first-return` and the desired source commit. It compiles only the exact dependency DAG and reports exported theorem axiom profiles. No new workflow is required.
