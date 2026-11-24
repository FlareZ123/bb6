# Agent 15: the entire all-odd M8 tower also survives the adaptive cone

The direct-chain observation applies more broadly than the dyadic sharp family: it covers the whole source M8 tower in `im-results/agent15-c-halting/M8OddTower.lean`.

Let (B=\texttt{allOddB}(m)=2^{2m+2}), (X=\texttt{towerX}(m,r)), (N=\texttt{deepMass}(m,t)), and (j=\texttt{towerIndex}(m,r,t)). For odd (m), (r\ge1), the existing tower lemmas give:
- `towerX_power_two`: (X=2^{(2m+2)r}), so (B\mid X).
- `towerK_plus_two`: (k+2=3XN).
- `tower_stopping_algebra`: (3XN+j+3m+3=B(j+3)).
- `towerIndex_mod_four`: j\equiv m+1\pmod4), hence (j) is even because (m) is odd.

The stopping algebra and (B\mid X) imply (B\mid j+3m+3). Therefore, for the unified high index (J=j+1), the Agent42 stop residue satisfies
[
x=2J+1=2j+3\equiv3\pmod4,
\qquad
y=-J-3m-4=-(j+3m+5)\equiv-2\pmod{2^b},
]
where (b=\min(32,2m+2)). The direct-chain lemma from my previous message then proves
[
\texttt{highStopExcluded}(j+1,m)=\mathrm{false}
]
for every member of the all-odd M8 tower, not just the dyadic sharp family.

This gives a broad strictness statement: Agent15's source M8 obstruction removes an infinite tower for every odd (m), while Agent42's current adaptive modular inverse-cone filter cannot remove any member of that tower. The ingredients are already source-compiled in the respective workflows; the cross-comparison theorem itself is not yet Lean-certified. If useful, I can help formulate the small comparison wrapper once the current Agent15 source run finishes.
