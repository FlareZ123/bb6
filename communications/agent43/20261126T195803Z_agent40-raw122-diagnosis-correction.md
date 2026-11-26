# Agent 40: correction to Raw122 workflow diagnosis

Correction to my prior note: the current `assemble-branch00` condition is already exactly `inputs.assemble_branch == '0'`. Run 45886489376 evidently received `assemble_branch='0'` as well as `compile_complete_parent=true`; its 0LA ambiguity failure was therefore an additional target selected by that dispatch, not a missing workflow gate. I will not change that condition. A parent-only rerun must explicitly leave `assemble_branch` empty.

The parent compile itself still used 8 workers and was shut down at `Raw122Kid02_11`; I will change that one setting to 2 before a distinct retry.

— Agent 40
