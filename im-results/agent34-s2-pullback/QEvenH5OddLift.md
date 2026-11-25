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

For the odd coset \(n=2r+1\),
\[
j=1343+2^{21}n=2098495+2^{22}r,
\qquad
m=2779178+2^{21}n+2^{23}w
 =4876330+2^{22}r+2^{23}w.
\]
The high-stop value is
\[
K=2^{2m+2}(j+3)-(j+3m+5).
\]
The exact arithmetic identity
\[
j+3m+5+49726=2^{23}(2+2r+3w)
\]
gives the parameterization
\[
K=49726+2^{23}b,\qquad
b=2^e(j+3)-(2+2r+3w),
\]
where
\[
e=9752639+8388608r+16777216w.
\]
This identity is now formalized by **h5OddK_gate** in the Lean bridge below.

The even coset \(n=2d\) is the parameter family in Agent 4's theorem
**blank_ne_s2q_even_image_h5_progression**. Its exact source proof is in
**im-results/agent4-c-seven-image/CSixSeventhS2QEven.lean**.

## Agent25 quarter source: exact parameter match, guarded subfamily

The AffineH5Quarter source defines
\[
h5J(r)=2098495+2^{22}r,\qquad
h5M(r,w)=4876330+2^{22}r+2^{23}w.
\]
These are exactly the \(j,m\) progressions above. The Lean CI log for run
[45644768030](https://github.com/FlareZ123/bb6/actions/runs/45644768030)
prints both definitions and successfully compiles the wrapper
**h5OddQuarterSource**. Therefore h5QuarterHighSource applies to this
odd-coset family whenever its phase guard holds and \(K\) satisfies the
high-stop equation.

The guard is
\[
(5r+3w+4)\bmod8=0
\quad\lor\quad
(5r+3w+17)\bmod16=0
\quad\lor\quad
\exists t\in\{26,48,51,56\},\
(37r+3w+t)\bmod64=0.
\]
It covers one quarter of the \((r,w)\) parameter lattice. This is a genuine
source-certified exclusion for that guarded subfamily, not a closure of the
entire odd-coset family. The exact Lean source and certificate are in
im-results/agent25-c-odd-lift/; CI run
[45531058201](https://github.com/FlareZ123/bb6/actions/runs/45531058201)
compiled the quarter-source module with the standard axiom set.

Do not conflate this \(2^{22}/2^{23}\) quarter source with Agent25's
separate 48-node highStopSource, whose progression uses \(2^{38}\).
The latter is a different, narrower subcylinder.

## New unconditional mass non-power lemma

For the odd-coset state
\[
\begin{aligned}
E_{ax}&=1735479+3388496r+6776976b,\\
E_{ay}&=1280448+2500056r+5000120b,
\end{aligned}
\]
define
\[
\begin{aligned}
T&=2^e(j+3), &D&=2+2r+3w, &b&=T-D,\\
Q&=376991+736069r+1472137b,\\
C&=2567283+2208205r+4416411w.
\end{aligned}
\]
Direct coefficient collection gives
\[
E_{ax}+E_{ay}+1=8Q,\qquad Q+C=1472137T.
\]
Also
\[
j+3=2(1049249+2^{21}r),
\]
so \(2^{e+1}\mid T\), hence \(2^{e+1}\mid Q+C\). The positive correction
satisfies
\[
0<C<e+1\le2^e.
\]
Writing \(p=2^{e+1}\), the residue \(Q\bmod p\) is therefore
\[
Q\bmod p=p-C>2^e.
\]
A power of two has residue either zero modulo \(p\), if its exponent is at
least \(e+1\), or at most \(2^e\), if its exponent is at most \(e\).
Consequently \(Q\) is never a power of two, and neither is
\(E_{ax}+E_{ay}+1=8Q\).

This is formalized in
im-results/agent34-s2-pullback/QEvenH5OddAgent25Bridge.lean by
**h5OddQ_not_pow**, **h5OddMass_eq**, and **h5OddMass_not_power**.
It removes the pure-power exception from the complete odd/even parent
classification for every \(r,w\), not merely the quarter-guard subset.

## Exact original-source parent fan

The same Lean module proves **h5Odd_parent_fan**, an instance of
**BB6.Agent3OddEvenFan.blank_reach_iff_odd_even_nonpower_parent_fan**.
For every \(r,w\), blank-root reachability of \((E_{ax},E_{ay})\) is
equivalent to one of exactly these alternatives:

1. Reachability of the direct parent
   \[
   (E_{ax}+E_{ay}-2,\ (E_{ay}-2)/2);
   \]
2. Reachability of an odd-depth, odd-left high-bounce parent \((a,k)\)
   satisfying
   \[
   n\bmod2=1,\quad a\bmod2=1,\quad 3\le a<2k,
   \]
   \[
   E_{ax}+E_{ay}+1=2^{n+1}(a+3),\qquad
   2k+a+7+3n=E_{ax}+2E_{ay}.
   \]

The equivalence is source-level: it is stated in terms of the original
run secNext (some (5,1)) semantics, not a surrogate recurrence. The
formal build passed in [CI run 45644768030](https://github.com/FlareZ123/bb6/actions/runs/45644768030).
This does **not** establish that either parent is reachable; it gives the
complete obligations that must now be discharged.

## Remaining odd/even high-valuation parent

The state \((E_{ax},E_{ay})\) has odd left coordinate and even right
coordinate, with
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
When \(r+b\not\equiv3\pmod4\), its sum is divisible by \(4\) but not \(16\),
and its low-value inverse is
\[
\begin{aligned}
P_x&=1828072+3569290r+7138578b,\\
P_y&=1234146+2409659r+4819319b.
\end{aligned}
\]
When \(r+b\equiv3\pmod4\), deeper 2-adic branches occur.

The unresolved work is to eliminate the direct parent and every admissible
odd-depth high-bounce parent uniformly, especially outside the quarter
guard. The base point \(r=w=0\) fails the Agent25 phase guard and remains
a useful adversarial test case.

## Cross-filter diagnostics (not a new theorem)

Agent 42's accepted 32-bit adaptive modular high-stop filter is another
source-certified exclusion mechanism. For the base odd-coset parameter pair
\(r=w=0\), its exact probe.py recurrence returns false, and Agent 25's six
guards also fail. This only says those two particular filters do not certify
that instance; it does not imply that the target is reachable, and other
source filters have not been exhausted here.

A small 16-by-16 diagnostic evaluation of Agent 42's 32-bit recurrence
accepted all sampled Agent 25 guard cases. This is not a proof of
containment or a full-period overlap audit. Agent 25's own memory explicitly
makes no novelty claim relative to all previous modular sieves. Therefore
do not count its quarter as additional global coverage until the overlap
with existing filters is established.

## Next mathematically useful work

1. Resolve the direct parent for the unguarded base point and then seek a
   uniform modular/source invariant for the remaining direct-parent family.
2. Use the explicit correction \(C\) and the 2-adic valuation of \(Q\) to
   enumerate and eliminate the entire odd-depth high-bounce fan, rather
   than checking only its first parent.
3. Audit overlap with Agent 42's and other accepted source filters before
   claiming any combined coverage.
4. Keep further parameter slices in im-results/ until their original
   source-parent obligations are completely discharged.
