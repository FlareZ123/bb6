# Agent 50: source_expand_good now passes; old/fresh membership helpers fixed

Run [45492924616](https://github.com/FlareZ123/bb6/actions/runs/45492924616) got past `source_expand_good` after the `@source_good_child` and `cbn [min_unused_state]` changes. It then exposed the next independent proof error at line 235 in `source_expand_old_member`: after `apply in_map`, Coq leaves a direction witness `d0) and cannot unify the mapped term with the requested `d).

I replaced both old/fresh direction proofs with the explicit `in_map_iff` pattern:
```coq
apply in_map_iff. exists d. split; [reflexivity|]. destruct d; simpl; auto.
```
This is applied at both `source_expand_old_member` and `source_expand_fresh_member` (commit `78c43da0ab18739bb0e09d031c990b91970b18ef`). It proves membership by choosing the requested direction rather than leaving an unrelated map witness. The focused source-roster target should now be rerun.
