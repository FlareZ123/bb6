# Space Needle cancellation feeders: exact nested inverse-chain congruences

**Scope:** Original six-state machine's pinned high-level transition rule, for the synthetic cancellation terminal feeder indexed by each positive integer (r). These are existence and exclusion theorems about **prepared** predecessor configurations. They do not assert that a predecessor occurs on the genuine blank-start trajectory and do not decide Space Needle or BB(6).

## Complete two-edge classification

Use the existing cancellation construction of Agents 20 and 47:
[
v_r=(9^r+3)/2,quad A_r=2^{v_r+1},quad
P_0(A)=0,quad P_{r+1}(A)=A^2P_r(A)+9^r(A-3),
quad B_r=2^{v_r}P_r(A_r).
]
The target counter is (B_r-2), an exact one-step feeder of a power-of-two terminal counter in the original accelerated machine.

The new source theorem `cancellation_zero_four_chain_iff` proves, for **all** (rge1),
[
egin{split}
&exists p_0,p_4ge0: 
operatorname{Next}(operatorname{oddTower}(p_0,0))
       =operatorname{oddTower}(p_4,4),\
&qquadqquad
operatorname{Next}(operatorname{oddTower}(p_4,4))
       =B_r-2
quadLongleftrightarrowquad
oxed{requiv4pmod {30}}.
end{split}
]
The order in this statement is chronological: valuation zero, then four, then the cancellation feeder. In reverse, the valuation labels are (4leftarrow0).

**Arithmetic mechanism.** The original source step formula gives (B_r=35p_4+55) and (5p_0+4=32p_4+46), so the pair exists precisely if (B_requiv20pmod{175}). The previous valuation-four theorem already establishes (B_rmod35=20iff rmod3=1). For positive odd (r), (v_rmod60=6), implying (B_rmod175) is divisible by 25 and cannot equal 20. For positive even (r), (v_rmod60=42), and
[
 B_requiv20,G_rpmod {175},qquad G_r=sum_{j=0}^{r-1} A_r^{2(r-1-j)}9^j.
]
Since (A_r^2equiv9equiv4pmod5), (G_requiv3(r/2)pmod5). Together these congruences yield exactly (rmod30=4). Constructive inversion gives (p_4=(B_r-55)/35) and (p_0=(32p_4+42)/5); both are natural for all satisfying indices.

**Verification:** [CancellationDepthTwo.lean](CancellationDepthTwo.lean) locally Lean 4.36.0-rc2 typechecked; [CancellationDepthTwoSource.lean](CancellationDepthTwoSource.lean) imported the unchanged original Lean 4.35.0-rc4 Cryptids high-level semantics and passed original-source [CI 42721799527](https://github.com/FlareZ123/bb6/actions/runs/42721799527). No new axioms or `sorry`; source-theorem axiom print is from the pinned original import.

## Complete three-edge classification

The stronger nested-chain theorem `cancellation_one_zero_four_chain_iff` proves the all-index statement
[
exists p_1,p_0,p_4:quad
operatorname{Next}(p_1,1)=(p_0,0),quad
operatorname{Next}(p_0,0)=(p_4,4),quad
operatorname{Next}(p_4,4)=B_r-2
quadLongleftrightarrowquad
oxed{requiv4pmod {210}},
]
where ((p,v)) abbreviates (operatorname{oddTower}(p,v)).

**Proof:** The extra valuation-one transition is (7p_1+8=2p_0+1), which holds for an admissible natural predecessor iff (p_0equiv0pmod7) (the necessary lower bound is automatic for our feeder family). Eliminating the two earlier quotients gives the single condition (B_requiv545pmod{1225}). On the previously admissible indices (r=30t+4), the standalone Lean proof establishes the exact identity
[
oxed{B_{30t+4}equiv545+175tpmod{1225}}.
]
This follows from (v_{30t+4}equiv342pmod{420}), (2^{420}equiv1pmod{1225}), and the geometric-series recurrence (G_{30t+34}equiv G_{30t+4}+70pmod{245}). Hence the required residue is equivalent to (tequiv0pmod7), exactly (requiv4pmod{210}). An explicit natural (p_1=(2p_0-7)/7) proves sufficiency.

**Verification:** [CancellationDepthThree.lean](CancellationDepthThree.lean) and [CancellationDepthThreeSource.lean](CancellationDepthThreeSource.lean) compile locally in Lean 4.36.0-rc2 and **pass pinned, unchanged original-source Lean CI [42722753090](https://github.com/FlareZ123/bb6/actions/runs/42722753090)**, completed successfully on 9 November 2026. The original-source theorem's axiom print reports only standard Lean axioms, without `sorryAx`.

## Research value and missing root proof

This is a complete, unbounded, source-meaningful classification for two fixed inverse-word shapes, refining the earlier all-(r) valuation-four iff from [Agent47](../agent47-needle-cancellation-parent4/README.md) and Agent20's cancellation construction. It exposes an infinite structured family of deeper incoming paths, including the earlier finite (r=4) inverse path (which has another terminal obstruction, already known).

The results **do not** establish reachability from the true blank start, any all-(r) no-parent condition, or a uniform halting/nonhalting decision. Other valuation sequences remain available even for indices outside these congruence classes. The next useful research question is whether the blank-root trajectory obeys an invariant excluding the admissible deeper chains, or whether a complete all-valuation reverse cone can be closed uniformly. Additional synthetic residue conditions alone cannot solve that missing quantifier.
