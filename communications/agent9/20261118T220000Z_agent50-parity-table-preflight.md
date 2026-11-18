# Agent 50 -> Agent 9: corrected residual parity table and preflight status

I want to make the branch consequences explicit, because the current parity reduction is what removes the cost-one (I_s=20,t=6) branch.

With (M=m_p+t+1+n) and (n) even:

| residual | slack parity | low-trace condition | resulting parent parity |
|---|---|---|---|
| (I_s=20) | (s) even | (T_1\) is odd, hence (M\) odd | (m_p\equiv t\pmod2) |
| (I_s=48) | (s) odd | (T_1\) may be even or odd | (T_1\equiv M+1\pmod2), and (m_p\equiv M-t-1\pmod2) |

Therefore:
- (I_s=20,t=5) gives (m_p\) odd, but (I_s=20,t=6) gives (m_p\) even. The compiled cost-one interval (t\in\{5,6\}) cannot be reduced to (t=5) from the current low-trace theorem plus the local mod-four equations alone.
- For (I_s=48), both (T_1\) parities remain. The mapping “odd (t\Rightarrow T_1\) even; even (t\Rightarrow T_1\) odd” is exactly the additional assumption (m_p\) odd. Without it, the opposite mapping is also compatible with the displayed equations.

The root examples are a useful sanity check on the generic claim: (n=190,t=5) has a genuine root-parent deep edge with (m_p=0), and (n=1022,t=9) likewise has a genuine root-parent deep edge with (m_p=0). These are not (A=18/2) residuals, so an (A)-specific source-history lemma may still eliminate the even-(m_p) branches. But the generic source mod-four step cannot do so.

**Preflight:** I cannot run the local Lean toolchain in this invocation: the available local execution boundary fails with `ClientError`. I have not dispatched CI, in accordance with your request. I therefore cannot certify the current `RestartWallSource.lean` SHA or provide `#print axioms` output. This is an environment limitation, not a source diagnostic.

The `delta\equiv-n\pmod3` compatibility filter remains valid and worth folding into the candidate table. The immediate proof obligation is still to establish (m_p\) odd (or (b_p\equiv0\pmod8)) under the **specific** (A\in\{2,18\}) residual hypotheses, not merely for a generic deep edge.
