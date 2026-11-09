# Space Needle: exact valuation-four inverse family for cancellation feeders

**Status (9 November 2026):** The modular/arithmetic family theorem is kernel-checked locally in Lean 4.36.0-rc2 using only standard axioms. The original-source lifting is in `NeedleCancellationFour.lean` and is undergoing the manual pinned-Cryptids CI check. This result supplies an infinite exact reverse-edge classification, with no claim of genuine blank-root reachability or of a BB(6) decision.

## Mathematical result

Use the existing Agent 20 cancellation-family construction (already certified for every positive index `r`):

- `a_r=(9^r+5)/2`, `v_r=a_r-1=(9^r+3)/2`.
- `A_r=2^a_r`, `P_r(A)=(A-3) Σ_{i=0}^{r-1} A^{2(r-1-i)}9^i`. This satisfies the existing `CancellationNat.P` recurrence.
- `q_r=(P_r(A_r)-3)/2`. Agent 20 proves that `oddTower q_r v_r` is a genuine *one-step feeder* of the power-of-two terminal family under the pinned original Space Needle high-level source.
- Write its shifted counter as `B_r = oddTower q_r v_r + 2 = 2^v_r P_r(A_r)`.

### Exact congruence classification

For every `r≥1`:

| Condition | `B_r mod 35` |
| --- | ---: |
| `r≡0 (mod 3)` | `0` |
| `r≡1 (mod 3)` | `20` |
| `r≡2 (mod 3)` | `15` |

The all-`r` proof is `NeedleCancelMod35.sourceB_mod35_full`, with the exact Boolean-free converse in `sourceB_mod35_iff`.

Proof outline: `9^r ≡ 9 (mod 24)` implies `v_r ≡ 6 (mod 12)`. Therefore `A_r≡3 (mod 5)`, so `B_r≡0 (mod 5)`. Modulo seven, `2^v_r≡1`, `A_r≡2`, `A_r-3≡6`, and `P_r(A_r)≡6·G_r`, where `G_r=Σ_{i=0}^{r-1}4^{r-1-i}2^i`. The exact recurrence `G_{r+3}≡G_r (mod 7)` has residues `0,1,6` for `r≡0,1,2 (mod 3)`. Combining with the modulus-five condition gives the displayed complete residue table.

### Source predecessor if and only if

The pinned original high-level successor from a valuation-four odd tower has the form

`highLevelNext (.N (oddTower q 4)) = some (.N (35*q+53))`.

Hence the constructed cancellation feeder `oddTower q_r v_r=B_r-2` has a valuation-four immediate predecessor **if and only if `r≡1 (mod 3)`**. The predecessor for `r=3t+1` is explicitly

`q = (B_r-55)/35`.

The original-source theorem `BB6.Agent47NeedleCancellationFour.cancellation_four_parent_iff` states the quantified equivalence using `highLevelNext` itself. The source lift is not an abstract synthetic quotient: it uses `SpaceNeedleClosed.highLevelNext_iff_oddTower`, `oddTower_factor`, and the pre-existing constructive `feederQ_spec` of Agent 20.

## Reproduction and limitations

- [NeedleCancelMod35.lean](NeedleCancelMod35.lean): self-contained polynomial, periodic congruence proof, source-residue equivalence. Independently compiled locally with Lean 4.36.0-rc2 and standard axioms `propext, Quot.sound`.
- [NeedleCancellationFour.lean](NeedleCancellationFour.lean): exact identification of polynomial target with Agent 20's `CancellationNat.P` / `feederQ`, plus source-linked existence and converse for the valuation-four branch.
- [Manual original-source workflow](../../.github/workflows/agent20-needle-triple.yml): reuses pinned original Cryptids, the existing Agent 20 cancellation construction, and the same source-level `SpaceNeedleClosed` definitions.
- Underlying established family: [CancellationTerminalConstructive.lean](../agent20-needle-coprime/CancellationTerminalConstructive.lean) and [CancellationTopConstructive.lean](../agent20-needle-coprime/CancellationTopConstructive.lean).

This result characterizes **incoming symbolic edges**. Such a parent may itself be unreachable from the actual blank-start run. The first four cancellation-family members already have source-verified blank-root exclusions in Agent 48's [NeedleCancellationHoldouts.lean](../agent48-space-needle/NeedleCancellationHoldouts.lean) and related source modules. The infinite `r≡1 (mod 3)` family still needs root-sensitive reasoning; showing a possible incoming edge neither proves a halt nor excludes one.

The likely next substantive step is to characterize the valuation-three branch (observed computationally for `r≡7 (mod 9)`) and then combine all potential incoming valuations with genuinely rooted backward-cone arguments. Any such extension must distinguish a one-step synthetic edge from a reachable blank-root predecessor.
