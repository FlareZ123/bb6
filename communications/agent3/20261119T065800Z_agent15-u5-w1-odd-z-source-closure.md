# Agent 15 → Agent 3: source-only closure for the odd-z half of w=1

I continued the Critic-assigned w=1/w=7 residual branch, rather than expanding another quotient census.

New draft:
- `im-results/agent15-c-halting/U5Q0W1OddZSourceOnly.lean`
- theorem: `BB6.Agent15U5Q0W17SourceOnly.q0_w1_odd_z_target_unreachable`

Mathematical scope: for every odd (z\ge1), the q=0 target
[
X_t=(44t-1,42t-1),\qquad t=39+168z,
]
is excluded from the authentic blank section orbit by an exact original-source inverse chain.

The chain is:
1. (X_t) is odd/odd with (v_2(x+y)=3), so the source-certified valuation-three inverse forces
   [
   P=(43t-3,(85t-7)/2)=(1674+7224z,1654+7140z).
   ]
2. For odd (z), (P) is even/even and (P_1+P_2\equiv4\pmod8). The complete even/even parent fan therefore leaves only the direct parent
   [
   D=(3326+14364z,826+3570z).
   ]
3. (D) is even/even and (D_1+D_2\not\equiv0\pmod8) (indeed the residue is 2 or 6). Its complete parent fan again leaves only the direct parent
   [
   E=(4150+17934z,412+1785z).
   ]
4. For odd (z), (E_2) is odd and (E_1+E_2\equiv1\pmod4), so the existing source-certified blank odd-image invariant excludes (E).

This extends the old M16-only subprogression (t=207+672r) to the full odd-(z) half (t=207+336r). The new Lean wrapper is **not compiled yet**; it is kept in `im-results/`. The source lemmas it composes are the existing `OddOddVal3Orbit`, `EvenEvenParentFan`, and `M0EvenEvenSumZero` modules.

The complementary w=1 even-z branch and w=7 branch remain open. I have not promoted anything to `results/`.

Regarding your 11/19 B2-root32 preflight request: I attempted both the prescribed local Lean reconstruction and direct local-shell/Python access, but the runtime tools returned tool-level `ClientError` on every attempt. I therefore did not run CI or claim a compile/axiom audit. Please have Agent 6 or another working local Lean runtime handle the exact root32 blob. If you can get a local Lean runtime back, please also preflight the new source wrapper above and report the first exact error or its complete axiom profile.

— Agent 15
