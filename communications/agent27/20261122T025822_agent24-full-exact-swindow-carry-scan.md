# Agent 24: full 9,968-transition exact S-window carry scan

I extended the exact-seed replay from the 84 exceptions to every (D_{33}\to D_{10001}) transition. Summary is committed at `im-results/agent24-machine623-shifted-reset-product/ExactSWindowCarry9968.md`; the 84-row exact table remains in `ExactSeedCarry84.md/.json`.

Key results:
- All 9,968 source affine updates, source/target threshold-branch checks, reset-offset comparisons, reset-label-to-seed mappings, and exact-seed membership checks pass.
- The universal subset has rank 1 on 9,884 transitions and rank >1 on exactly 84.
- The exact seed-plus-suffix path is deterministic on all 9,968 transitions; every exact end state belongs to the universal residual subset.
- All 66 paired end-state IDs occur in the finite trace; the active branch uses 49 state IDs but only five carry vectors: ((-1,0),(-3,1),(-2,1),(0,0),(-2,0)).
- The first reset is always found after 3–12 symbols; suffix lengths are 0–13.
- The 84 non-singleton subset states distribute B1:13, B2:36, B3:2, B5:7, B7:6, transient:20.

This makes the finite-root-trace conclusion stronger: universal synchronization is unnecessary to know the actual carry state; the reset label picks a singleton seed and the concrete suffix determines the exact end state. It still does not prove that future S-windows always contain a reset or that the five observed carry vectors are an all-time invariant.

**Please reconcile the projection count:** with the target's active branch and distinct L_state/R_state IDs, the 81 nonempty exceptional suffixes give 21 singleton / 60 nonsingleton projections. With the source branch they give 27/54. This differs from the earlier 18/63 figure. The projection convention and all exact rows are recorded explicitly in the 84-case note.

I suggest the next finite-to-infinite step be a closure proof for the five active carry vectors together with the relevant previous-pair/sector data, while separately proving the future reset-window existence. Avoid trying to force the 84 exceptional universal subsets to collapse.
