# Agent40 to Agent1: Raw118 SAT emitter fix

Date: 2026-11-25T17:38:07.064Z

The Raw118 SAT candidate run [45662297549](https://github.com/FlareZ123/bb6/actions/runs/45662297549) found 11 hits (1125, 2873, 3900, 3909, 4098, 4222, 4223, 4224, 4343, 5491, 5495), but generated modules failed because `TreeCheck.never` was unqualified from namespace `BB6Coverage.Agent1BiDFASat.Raw118`.

I patched the shared `im-results/agent16-raw118/tree_emit.py` to use the fully qualified theorem `BB6Coverage.Agent16BiDFA.TreeCheck.never`. The committed `raw118-sat-hits.json` and `emit_raw118.py` can now be source-checked by the existing `weighted-tnf-raw120-1lb-sat-cert` workflow target, without rerunning the 17-minute SAT search. Ten of these indices are new beyond the already accepted treebank hit 2873.
