# Agent 42 review: parent-cone CI failure and concrete repairs

I added a selective push trigger to the existing even-marker workflow and ran it at head `3b04989860d70dd00f56961aa20405a682c85566` (run [43325173229](https://github.com/FlareZ123/bb6/actions/runs/43325173229)). Lean installed correctly. The workflow currently stops at `Root119B0ParentCone.lean`; it does **not** reach my downstream composition module. The source draft is therefore not yet kernel-checked, and the error-recovery `sorryAx` reports are not theorem evidence.

The tight-corridor argument itself looks structurally sound: equality in the path-length/head-displacement bound forces every edge left; a B/0 intermediate is excluded because its C successor cannot return to B on an all-left path; the resulting F/0,B/1 corridor has exactly the offsets needed for the odd retreat. The current blockers are mostly concrete elaboration/index issues:

1. **Line 128: existential tuple order.** In `reached_F0_parent_split`, the second branch is `∃ f b, Reach f ∧ ... ∧ Reach b ∧ ...`. The current `⟨a,ha,...,u,Reach.follow ha hstepA,...⟩` puts `ha` in the second witness slot. Use `⟨a,u,ha,hFq,hzero,?,Reach.follow ha hstepA,hBq,hbit,?,hstepA,hstep⟩`.

2. **All ancestry `k` binders must be Nat.** Lean infers `k : Int` from the head-coordinate formula, then rejects `Root119Path (2*k+...)`. Explicitly annotate the existential binder as `∃ k : Nat, ...` in `reached_F0_D1_successor_path`, `reached_F0_D1_ancestor`, `reached_F0_F1_ancestor`, `reached_B0_left10_D1_ancestor`, `reached_B0_left10_F1_ancestor`, `reached_B0_left10_path_components`, `reached_B0_left10_odd_seed_conditions`, and `reached_B0_left10_left_tape_agreement`. Keep the coordinate cast explicit as `(2*(k:Int))`.

3. **Strong induction name/case.** The current `Nat.strong_induction_on` is unavailable in this source import closure. Repository source uses `Nat.strongRecOn` with case `ind n ih`; replace both the induction constant and case label.

4. **Line 462, `parentCone_next_tape_away`.** After `simp [next,hb] at hs`, the constructed successor has not been substituted for `d`. Add `all_goals cases hs` before simplifying the `setBit` goal. This is why all transition cases leave `d.tape x = t x` unsolved.

5. **Line 500, `parentCone_next_left_preserves_noBF`.** Same issue: split q/read, simplify `hs`, then `cases hs` so the target state/head are exposed before the `parentConeNoBF` and left-head checks. The current `omega` calls have no usable constraints because `d` remains opaque.

6. **Lines 517/540: induction-hypothesis implicit parameters.** After reverting `c d`, the induction hypothesis expects its explicit argument to be the path, not `u`. Apply it with named implicit arguments, e.g. `ih (c := u) (d := d) ht hdispTail ...`. Also line 538 omits the cell argument: call `parentCone_next_tape_away c u hs x (by omega)`, not `... hs (by omega)`.

7. **Line 559: Nat/Int cast.** The equality `2*(k+1)+1=(2*k+2)+1` is Nat, while `hdisp` contains a cast to Int. Give `omega` an explicit cast equality, e.g. `have hlenInt : ((2*(k+1)+1:Nat):Int)=(2*k+3:Int) := by omega`, then simplify `hdisp` with `hlenInt`.

8. **Core tactic availability.** The `by_contra` uses at the B-bit split and k-positivity proof are reported as unknown tactics under this workflow's imports. Replace with `by_cases hb : b.tape b.h = true` / `by_cases hk : 1≤k` and eliminate the negative branch using Bool cases and arithmetic.

9. **Line 777: normalize the tape index explicitly.** `hp1.2` simplifies to `e.tape (e.h-3)=true`, while the target is `e.tape (f.h-1)=true`. Prove `hidxLeft' : e.h-3=f.h-1 := by rw [hposE]; omega`, then `rw [← hidxLeft']; exact hp1.2`.

10. **Lines 781/790:** `le_rfl` is not in this import closure; use `by omega` for reflexive head bounds. Lines 786/795 rewrite in the wrong direction: use `hidxF.symm` / `hidxB.symm` when the goal contains `g.h` / `c.h`. The later Nat-vs-Int errors at 821/823 are again fixed by the explicit Nat binder in item 2.

I have kept my downstream module separate at `im-results/agent42-root119-guard/Root119B0OddWaveComposition.lean`. Once this parent module compiles cleanly, it composes the exact corridor with `odd_f1_to_b` for k=1 and `odd_f1_retreat_to_b0` with m=k−2 for k≥2, and identifies the full returned configuration with the reached B/0 endpoint. I will not report that composition as verified until the parent source and the new module both pass the fail-closed workflow.
