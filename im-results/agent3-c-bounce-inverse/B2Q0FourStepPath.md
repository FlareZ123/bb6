# B2 target to q=0 parent: exact four-section path (Lean formalization pending)

## Statement suggested by the exact section map

For every natural parameter \(u\), define

\[
B_0(u)=(734+10944u,\;34881+518816u).
\]

The executable `BB6.Agent46.exactSection` definition in `im-results/agent46-c-jump/FastSectionDef.lean` gives the following four-step path:

| transition | target state | section duration |
|---|---|---|
| 1 | \(S_1(u)=(352256u+23690,\;348160u+23414)\) | \(1037632u+69769\) |
| 2 | \(S_2(u)=(360448u+24243,\;344064u+23141)\) | \(696320u+46830\) |
| 3 | \(S_3(u)=(393216u+26450,\;327680u+22041)\) | \(688128u+46281\) |
| 4 | \(Q(u)=(524288u+35269,\;262144u+17635)\) | \(655360u+44084\) |

The final state is exactly the q=0 parent in `U5Y3ParentFan`. With \(h=8+128u\),

\[
39+64h=551+8192u,
\qquad m+1=8(39+64h)+1,
\]
so

\[
(8(m+1)-3,\;4(m+1)-1)=Q(u).
\]

Thus the B2 target and q=0 parent share the *same* parameter \(u\), if the exactSection transition is identified with the source `secNext` relation.

## Branch derivation from FastSectionDef

For the first transition, the outer exactSection branch has

\[
a=734+10944u,\quad k=34881+518816u,
\]
with \(a>1\), \(k>0\), and

\[
2k-a=69028+1026688u>0.
\]
The `bounce` call is

\[
k_0=a-1=733+10944u,\quad c_0=2k-a+3=69031+1026688u.
\]
Here \(k_0\) is odd. Every odd recursive step sends \(k\mapsto2k+3\), \(c\mapsto c-(2k+3)\), and adds \(2k+4\) to the duration. Put \(A=736+10944u=k_0+3\). After \(n\) recursive steps,

\[
k_n=2^nA-3,\qquad c_n=c_0-(2^{n+1}-2)A+3n.
\]
The odd-stop gap is

\[
d_n=c_n-(2k_n+6)=c_0-(2^{n+2}-2)A+3n.
\]
For \(n=0,\ldots,4\), the gaps are positive; the minimum is

\[
d_4=348160u+23411>0.
\]
At \(n=5\),

\[
d_5=-352256u-23690<0.
\]
Moreover \(d_{n+1}-d_n=-2^{n+2}A+3<0\). Hence there are exactly five odd recursive steps followed by the odd stop. The final bounce state is \(S_1(u)\); the accumulated bounce duration is \(c_0+5\), so the exactSection duration is \(a-1+c_0+5=1037632u+69769\).

The remaining transitions stop immediately in their respective parity branches:

- From \(S_1\): bounce arguments \(k=352256u+23689\) (odd), \(c=344064u+23141\), with \(2k+6-c=360448u+24243>0\). The odd-stop output is \(S_2\), duration \(696320u+46830\).
- From \(S_2\): bounce arguments \(k=360448u+24242\) (even), \(c=327680u+22042\), with \(2k+8-c=393216u+26450>0\). The even-stop output is \(S_3\), duration \(688128u+46281\).
- From \(S_3\): bounce arguments \(k=393216u+26449\) (odd), \(c=262144u+17635\), with \(2k+6-c=524288u+35269>0\). The odd-stop output is \(Q\), duration \(655360u+44084\).

The outer condition \(2k>a\) holds at these three states with positive gaps respectively \(344064u+23138\), \(327680u+22039\), and \(262144u+17632\). All inequalities hold for every \(u\ge0\).

## Verification status and next step

The formulas were evaluated with the exact recursive equations at \(u=0,1,2,17,1802,8522,21962\); all four states and durations matched. The all-\(u\) branch inequalities above are an algebraic derivation from the copied `FastSectionDef` equations, but this note is **not yet a Lean-checked theorem** and does not by itself certify source reachability.

The next formal step is to prove the four equations using the exact `FastSectionDef` module and its `FastSectionProof` source-equivalence theorem, then connect the final `exactSection` output to `U5Y3ParentFan.secNext` and the q=0 parent branch. Agent 46 has been asked to review/formalize this exact path. Do not claim the same-candidate source link closed until that proof compiles against the unmodified source modules.


## Source equivalence hook

The exact source bridge is `BB6.Agent46.section_exact` in `im-results/agent46-c-jump/FastSectionProof.lean`:

```lean
run (secTime (a,k)) (some (a,k,0)) = (secNext (a,k)).map embed0
```

A formal proof can establish each affine `exactSection` evaluation, then apply `section_exact` four times and compose the corresponding `run` segments. The final outstanding compatibility check is that the `secNext` relation used by `U5Y3ParentFan` (importing `SectionAllInverse`) is the same section transition as `BB6.Agent46.secNext`. Agent 46 has been sent the theorem name and the suggested composition. The existing manual workflow `.github/workflows/agent46-c-jump.yml` compiles the FastSection modules, but no CI was dispatched.
