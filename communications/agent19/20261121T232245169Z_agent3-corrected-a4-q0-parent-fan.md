# Agent 3 → Agent 19: correction and exact q=0 secondary fan

**Correction to my 2026-11-21T21:53Z message:** I reopened the actual section_preimage_all_iff definition. I had the parity of the odd-\(a\) high-bounce depth backwards. For target \(T_0=(X_0,Y_0)\) with \(X_0\) even and \(Y_0\) odd, the cost equation has right side \(X_0+2Y_0+2\), which is even, while its left side has parity \(n\). Therefore **\(n\) is even**, not odd. The earlier \(n=1,3\) parent list in that message is not a list of genuine section edges; please discard it.

The corrected exact fan is now in
im-results/agent3-c-bounce-inverse/Root32HighStopA4ParentFan.md.

For \(t=719+1024s\), the q=0 A4 parent is
\[
T_0=(1773156457998+2524388401920s,\;
1647558417041+2345578327680s)
\]
and \(H=T_{0,x}+T_{0,y}+1\) has exact \(v_2(H)=5\). The odd-\(a\) branch gives
\[
a=H/2^{n+1}-3,\qquad
k=(T_{0,x}+2T_{0,y}-H/2^{n+1}-4-3n)/2.
\]
The valuation bounds \(n\le3\), and parity leaves exactly \(n=0,2\):
- \(P_0=(1710357437517+2434983364800s,\;1678957927278+2390280846240s)\), with residues \((5,6)\pmod8\), sum \(3\pmod8\).
- \(P_2=(427589359377+608745841200s,\;2320341966345+3303399608040s)\), odd/odd with sum \(2\pmod4\), hence excluded by the original-source odd-right image theorem.

The six-even-right inverse on \(P_0\) is exact and gives
\[
R_0=(3389315364793+4825264211040s,\;
839478963638+1195140423120s).
\]
Thus **Reach(T0) iff Reach(R0)**. The residual has \(R_{0,x}\equiv1,\ R_{0,y}\equiv6\pmod8\) and
\[
R_{0,x}+R_{0,y}+1\equiv16+16s\pmod{32}.
\]
For even \(s\), your sumseven_forced_root_iff reduces it to
\[
R_1=(4228794328429+6020404634160s,\;
419739481818+597570211560s),
\]
where \(R_{1,x}\equiv5,\ R_{1,y}\equiv2\pmod8\) and the sum-plus-one is \(8\pmod{16}\), so the exact mod16_seven_blank_reach_iff two-parent split applies. For odd \(s\), \(R_0\) has sum-plus-one \(0\pmod{32}\), not your current sum-seven root gate.

For \(t=79+512s\), the q=0 parent similarly has \(v_2(X_0+Y_0+1)=4\), so only \(n=0,2\) survive:
- \(P_0=(188492834517+1217491682400s,\;185032398378+1195140423120s)\), with \((x,y)\equiv(5,2)\pmod8\). Its second sum-seven root gate applies on \(s\equiv7\pmod8\).
- \(P_2=(47123208627+304372920600s,\;255717211320+1651699804020s)\), with \(x\equiv3\pmod8,\ y\equiv4s\pmod8\). The high-even-right sum-seven exclusion applies on \(s\equiv1\pmod8\); for even \(s\), the six-even-right inverse applies but is not yet a full exclusion.

No full q=0 exclusion is claimed for either cylinder. This is a corrected exact source-parent reduction, not a new residue cylinder. The note also records that local Python/container tools currently fail with ClientError, so no Lean acceptance is claimed.
