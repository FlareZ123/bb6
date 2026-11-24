# Critical P1 right-five gate as a guarded first return

**Mathematical claim.** For every n≥14 put Q=7·2^n−n−3. An original-source odd inverse history from (14·2^n−2n−16,3) to any (b,5) exists exactly when some q≥5 and k>0 satisfy q+k=Q, the moving-modulus recurrence r_0=1, r_j=2r_(j−1) mod (q+j) has its first positive return to 1 at j=k, and each wrap satisfies r_j+8≤q+j. This reduces the right-five gate itself, not blank-start reachability of every P1 terminal or BB(6).

**Proof status.** Original-source equivalence passed the exact dependency-closure Lean 4.36.0-rc2 workflow at commit 62e88e75ccf52af7c3fd872d32e3168c7a6f745b ([run 45508108201](https://github.com/FlareZ123/bb6/actions/runs/45508108201)). The new cost bound below passed local core compilation and interface preflight; full-source validation is pending.

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

## Remaining mathematical target

The recurrence is the Borwein–Loring recursion a_(t+1)=2(a_t mod t), with a_(q+j+1)=2r_j. See Borwein and Loring, *Some Questions of Erdős and Graham on Numbers of the Form sum g_n/2^g_n* (1990), and Dearden and Metzger, *Running Modulus Recursions* (2010), https://cs.uwaterloo.ca/journals/JIS/VOL13/Dearden/dearden3.pdf. Eventual hitting of zero is conjectural generally and would not preclude earlier safe return to 1. Agent 3 previously identified this family for F118. The useful P1-specific target is now the absence (or exact construction) of guarded first returns at clocks Q=7·2^n−n−3 on the critical n classes, and its connection to the remaining blank-root exit cases.

## Reproduction

Use the existing workflow `.github/workflows/agent9-p1-shadow-depth.yml`, selecting `first-return` and the desired source commit. It compiles only the exact dependency DAG and reports exported theorem axiom profiles. No new workflow is required.
