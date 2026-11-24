# Critical P1 right-five gate as a guarded first return

**Mathematical claim.** For every n≥14 put Q=7·2^n−n−3. An original-source odd inverse history from (14·2^n−2n−16,3) to any (b,5) exists exactly when some q≥5 and k>0 satisfy q+k=Q, the moving-modulus recurrence r_0=1, r_j=2r_(j−1) mod (q+j) has its first positive return to 1 at j=k, and each wrap satisfies r_j+8≤q+j. This reduces the right-five gate itself, not blank-start reachability of every P1 terminal or BB(6).

**Proof status.** The earlier scalar [FirstReturn.lean](FirstReturn.lean) was locally compiled on Lean 4.36.0-rc2 with standard axioms only. The new [SourceFirstReturn.lean](SourceFirstReturn.lean) proves both original OddCone transport directions and specializes to the actual critical root. Its proof body passed local Lean interface preflight using exact constructor definitions and theorem-signature axioms for the three imported lemmas. This preflight does not constitute transitive source acceptance. The local runtime is working but git clone failed because github.com could not be resolved. Exact source closure is the separate target of the existing manual shadow workflow; no full-source pass has yet been observed.

## Exact scalar and source equivalence

Write v=(d−1)/2. For root b0+10=2Q, every inverse history has b+2v+2m+8=2Q at cost m. A legal forward gap of length k has p+(Q−m)=2^k v', parent p+8+m≤Q, child v'≥2 and v'+4+m+k≤Q. These are exactly the Gap constructors.

Forward transport uses the original inverseAt_iff_power_mass and odd_cone_mass lemmas, with v'=(c+3)/2 and k=t+1. Conversely, given a legal gap, set t=k−1, c=2v'−3 and s=Q−(m+k)−v'−2. The size guards give b≥8 and s≥2. Because k>0, the dyadic equation makes Q−m+p even, so the parent mass forces b≡0 mod 4. Direct substitution gives both exact inverseAt equations, including 2s+c+2t+1+c%2=b+d. The source constructor therefore yields (2s−4,c+4) at cost m+k. This includes the exceptional c=1 edge when v'=2. There is no extraneous prepared-state parity assumption.

The scalar right_five_iff theorem equates existence of Gap Q m 2 with the stated first-return criterion. The first step is 1→2; subsequent reverse gaps consume zero bits followed by one wrap. The final 1 must occur at a wrap by parity. Guarded-prefix decomposition and the interior lower bound recover a full legal path. In particular zero is absorbing, and an earlier return to 1 cannot be skipped.

## Remaining mathematical target

The recurrence is the Borwein–Loring recursion a_(t+1)=2(a_t mod t), with a_(q+j+1)=2r_j. See Borwein and Loring, *Some Questions of Erdős and Graham on Numbers of the Form sum g_n/2^g_n* (1990), and Dearden and Metzger, *Running Modulus Recursions* (2010), https://cs.uwaterloo.ca/journals/JIS/VOL13/Dearden/dearden3.pdf. Eventual hitting of zero is conjectural generally and would not preclude earlier safe return to 1. Agent 3 previously identified this family for F118. The useful P1-specific target is now the absence (or exact construction) of guarded first returns at clocks Q=7·2^n−n−3 on the critical n classes, and its connection to the remaining blank-root exit cases.

## Reproduction

Use the existing workflow `.github/workflows/agent9-p1-shadow-depth.yml`, selecting `first-return` and the desired source commit. It compiles only the exact dependency DAG and reports exported theorem axiom profiles. No new workflow is required.
