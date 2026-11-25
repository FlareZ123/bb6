# Q-even h5 odd lift: exact partial source closure and remaining parent fan

## Exact parameter cylinder

The complementary q-even lift is
\[
u=2+4096n,\qquad v=48+8192b,
\]
with
\[
t=(u+v-2)/4=12+1024n+2048b,\qquad
z=(12+11t-v)/32=3+352n+448b.
\]
It satisfies
\[
53u+57v\equiv794\pmod{1024},
\]
equivalently the adjacent h5 lift \((2t-z)\bmod8=5\).

The corresponding high-stop parameters are
\[
j=1343+2^{21}n,\qquad m=2779178+2^{21}n+2^{23}w.
\]
Since
\[
j+3m+5+49726=2^{23}(1+n+3w),
\]
the high-stop value
\[
K=2^{2m+2}(j+3)-(j+3m+5)
\]
satisfies \(K\equiv49726\pmod{2^{23}}\). Write \(K=49726+2^{23}b\); then \(v=48+8192b\).

The even coset \(n=2d\) is the parameter family in Agent 4's theorem **blank_ne_s2q_even_image_h5_progression**. Its exact source proof is in **im-results/agent4-c-seven-image/CSixSeventhS2QEven.lean**; do not call the new high-stop pullback an accepted source theorem without the corresponding focused CI/axiom audit.

## Source-certified odd-coset subcylinder

For \(n=2r+1\),
\[
j=2098495+2^{22}r,\qquad
m=4876330+2^{22}r+2^{23}w.
\]
This is exactly Agent 25's high-stop specialization. The original high-stop identity gives
\[
(2j+3,K)=(4196993+2^{23}r,\ 49726+2^{23}b).
\]

Agent 25's theorem **h5QuarterHighSource**, checked against the original Machine C section source in [CI 45531058201](https://github.com/FlareZ123/bb6/actions/runs/45531058201), proves \(\neg CReach(2j+3,K)\) whenever at least one guard holds:
\[
\begin{aligned}
5r+3w+4&\equiv0\pmod8,\\
5r+3w+17&\equiv0\pmod{16},\\
37r+3w+t&\equiv0\pmod{64}
\quad\text{for some }t\in\{26,48,51,56\}.
\end{aligned}
\]
The six disjoint classes occupy exactly \(16/64=1/4\) of the \((r,w)\)-parameter lattice. The CI dossier reports only [propext, Classical.choice, Quot.sound] for checkCertificate_sound, autoCheck_sound, quarterExcludes, h5QuarterHigh, and h5QuarterHighSource; no sorryAx is reported.

The reusable certificate is stored in compressed source form:
- im-results/agent25-c-odd-lift/QEvenH5OddCertificate.lean.xz.b64 (decoded SHA-256 d4d45b635a6736c7384164a24a619a339a7590c9ee379d9ec24161c007ab53b7);
- im-results/agent25-c-odd-lift/AffineH5Quarter.lean.xz.b64 (decoded SHA-256 af25d65ff7dcd1b4fdde3cf3058388ddb3a24fa79b65189ad49da7defdecb740).

The proof uses the complete original-source predecessor grammar, including the odd-bounce alternatives; it is not a direct-parent-only argument. This closes a genuine subset of the odd coset, not the full odd coset and not Machine C.

## Remaining odd/even high-valuation parent

For \(n=2r+1\), the state reached after the already established affine pullbacks is
\[
\begin{aligned}
E_{ax}&=1735479+3388496r+6776976b,\\
E_{ay}&=1280448+2500056r+5000120b.
\end{aligned}
\]
It has odd left coordinate, even right coordinate, and
\[
E_{ax}+E_{ay}\equiv7\pmod8.
\]
Thus the even-coset six-even-right guard does not apply.

The direct parent candidate is
\[
\begin{aligned}
E_{bx}&=3015925+5888552r+11777096b,\\
E_{by}&=640223+1250028r+2500060b.
\end{aligned}
\]
When \(r+b\not\equiv3\pmod4\), its sum is divisible by \(4\) but not \(16\), and its low-value inverse is
\[
\begin{aligned}
P_x&=1828072+3569290r+7138578b,\\
P_y&=1234146+2409659r+4819319b.
\end{aligned}
\]
When \(r+b\equiv3\pmod4\), deeper 2-adic branches occur.

The direct parent is not forced. For any odd/even target \((x,y)\) with \(x+y+1\) not a power of two, the exact original-source theorem
**BB6.Agent3OddEvenFan.blank_reach_iff_odd_even_nonpower_parent_fan**
splits blank-root reachability into:
1. the direct parent \((x+y-2,(y-2)/2)\); or
2. every odd-depth, odd-left high-bounce parent satisfying
   \[
   x+y+1=2^{n+1}(a+3),\qquad
   2k+a+7+3n=x+2y.
   \]
The unresolved work is to eliminate this complete high-bounce fan uniformly, or to find a different invariant for its remaining branches. Do not infer the formal direct-parent path from the existence of a direct parent.

## Cross-filter diagnostics (not a new theorem)

Agent 42's accepted 32-bit adaptive modular high-stop filter is another source-certified exclusion mechanism. For the base odd-coset parameter pair \(r=w=0\), its exact probe.py recurrence returns false, and Agent 25's six guards also fail. This only says those two particular filters do not certify that instance; it does not imply that the target is reachable, and other source filters have not been exhausted here.

A small 16-by-16 diagnostic evaluation of Agent 42's 32-bit recurrence accepted all sampled Agent 25 guard cases. This is not a proof of containment or a full-period overlap audit. Agent 25's own memory explicitly makes no novelty claim relative to all previous modular sieves. Therefore do not count its quarter as additional global coverage until the overlap with existing filters is established.

## Next mathematically useful work

1. Obtain Agent 25's exact theorem signature/import interface and check whether its accepted source module can be consumed directly by an Agent 34 bridge.
2. Analyze the complete odd/even high-bounce fan above, not just the direct parent. The parameter \(Q=376991+736069r+1472137b\) satisfies \(E_{ax}+E_{ay}+1=8Q\); high-bounce exponents are controlled by \(v_2(Q)\). Look for a uniform descent or a finite residue partition that closes all remaining branches.
3. Keep any new parameter classes in im-results/ until their original-source theorem and complete parent obligations are accepted. The odd coset remains unresolved outside the stated certified subset.
