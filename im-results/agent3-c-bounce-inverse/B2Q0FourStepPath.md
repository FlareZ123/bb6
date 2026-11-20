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


## Connection to the U5 residual parent theorem

The namespace check is resolved from the source headers: `SectionAllInverse.lean` defines `BB6.Agent46.secNext`, and `U5Y3ParentFan.lean` imports `SectionAllInverse` then opens `BB6.Agent46`. Its theorem `u5_residual_y3_parent_fan` states that, under the U5 residual equations and the high-stop successor condition, the q=0 branch is exactly

```lean
a=8*(m+1)-3 ∧ k=4*(m+1)-1
```

The terminal state Q(u) in the four-section path is precisely this `(a,k)) when `h=8+128*u` and `m+1=8*(39+64*h)+1`. Thus the all-u path, once formalized with `section_exact`, identifies the B2 target parameter with the q=0 parent parameter on the same `secNext` trajectory; the earlier concern about distinct `secNext` namespaces is not a blocker.

The remaining work is now narrower: kernel-check the four exactSection evaluations, and establish that the residual equations `hs/hm`, root affine residue, and root-index class are the ones supplied by the same blank-start candidate. This does not yet certify the full `U5B2Root32.lean` import closure or a BB(6) upper bound.


## Preferred formal proof route: SectionAllInverse iff

There is a simpler route than unfolding `FastSectionDef.bounce`. The already source-certified theorem `BB6.Agent46.section_preimage_all_iff` in `SectionAllInverse.lean` characterizes every original `secNext` edge (source-verified in CI 41544188316). The four transitions above follow directly from its arithmetic witness branches:

| edge | source parity | predecessor-grammar branch | witness depth |
|---|---|---|---:|
| B0 → S1 | even | `x+y=2^n*(2*(a-1)+6)` | 5 |
| S1 → S2 | even | `x+y=2^n*(2*(a-1)+6)` | 0 |
| S2 → S3 | odd | `x+y+1=2^n*(2*(a-1)+8)` | 0 |
| S3 → Q | even | `x+y=2^n*(2*(a-1)+6)` | 0 |

The companion linear equations in `sectionPreimageAll` reduce to the following exact equalities (both sides of the second equation):

- B0 → S1: `1048576*u+70518`.
- S1 → S2: `1048576*u+70525`.
- S2 → S3: `1048576*u+70534`.
- S3 → Q: `1048576*u+70539`.

The first sum identity is `x+y=700416*u+47104=32*(1472+21888*u)`; the next three are respectively `704512*u+47384=2*(352256*u+23692)`, `720896*u+48492=2*(360448*u+24246)`, and `786432*u+52904=2*(393216*u+26452)`. All side conditions are linear parity/positivity facts. This should allow a short Lean proof using four applications of `section_preimage_all_iff` and `omega), without importing the recursive FastSectionDef closure.

Since `U5Y3ParentFan.lean` imports `SectionAllInverse` and opens `BB6.Agent46`, the source relation is exactly the same `secNext` used by the q=0 parent theorem. Agent 15 has been asked to review/compile this direct proof route. It remains pending a kernel compile.


## Fifth edge: q=0 parent to the high-stop target

The q=0 parent Q(u) also has a direct original-section edge to the high-stop target

\[
T(u)=(70538+1048576u,3).
\]

In `section_preimage_all_iff`, Q has odd left coordinate, positive right coordinate, and \(2k=a+1>a\), so use the odd-a exceptional `y=3` branch with witness depth n=0:

\[
x+6=2^0(2(a-1)+8)=2a+6=70544+1048576u,
\]

and

\[
(2k-a+3)+(2(a-1)+8)=4+(70544+1048576u)
=70548+1048576u=x+10.
\]

Thus `secNext Q(u)=some (70538+1048576*u,3)`. Since \(m+1=4409+65536u\), we have \(m=4408+65536u\) and \(16m+10=70538+1048576u\). Therefore T(u) is exactly the high-stop target `(16*m+10,3)` used by `u5_residual_y3_parent_fan`.

The same-parameter source path is now five original-section edges:

\[
B_0(u)\to S_1(u)\to S_2(u)\to S_3(u)\to Q(u)\to T(u),
\]

with predecessor-grammar depth witnesses \((5,0,0,0,0)\). The first four edges are documented above; the fifth uses the odd-a/y=3 exceptional branch. This gives a direct B2-target-to-high-stop-target path, not merely a path to the q=0 parent. The five edge claims still await a Lean wrapper applying the existing source-certified iff; the arithmetic witnesses are explicit.


## Important remaining parameter identification

The five-edge path fixes the high-stop target parameter to

\[
m_{B2}=4408+65536u,
\qquad T(u)=(16m_{B2}+10,3).
\]

The separate arithmetic theorem `u5_residual_nonempty(w)` constructs some residual witness \((s,m_{res})\) satisfying hs/hm for each w, but its existence statement alone does not establish \(m_{res}=m_{B2}\). The q=0 residual parent theorem must be applied to the same high-stop target, so this equality (or a theorem showing the residual witness is exactly the parameter of the reached high-stop target) remains an essential source-link obligation. Do not infer it merely from the fact that both parameter families exist.


## Residual witness parameter is forced to match the B2 path

The remaining arithmetic equality `m_res=m_B2` can be derived from hs/hm and the root residue, rather than assumed. From `hm`, `m=8t). Combining hs and hm yields `211*t+1360+22155*w=20*2^(201+3360*w)`. Multiplying by 291 gives the exact identity

```
291*(211*t+1360+22155*w)
 = (w+4057*t+2544) + 8192*(787*w+7*t+48)
```

With `w=6657+8192*r`, divisibility by 8192 forces `4057*t+9201 ≡0 (mod8192)`. As `4057*105=1+52*8192`, we get `t≡551 (mod8192)`, hence `t=551+8192*u`, `m=4408+65536*u), and `h=8+128*u`. Therefore the residual high-stop parameter is exactly the one in the B2 five-edge path. This is an algebraic derivation; it still needs a Lean theorem and the same-candidate root residue premise.
