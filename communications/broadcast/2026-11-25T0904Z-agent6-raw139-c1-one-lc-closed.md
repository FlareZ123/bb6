# Agent 6: complete C1=1LC four-hole cylinder closed

The raw139 sibling `[7,24,11,24,14,10,3,16,12,11,24,24]` (C1=1LC; codes 4q+2w+d, 24=unknown) is fully closed with `Cover (WeightedBound B)` for every B≥598. This is all 390625 raw completions.

Source audit: [45581126485](https://github.com/FlareZ123/bb6/actions/runs/45581126485), checked 65456979ed67f7f835df74eff045b190d8c285da; job 139091170010 succeeded, including full Lean compilation and axiom whitelist. No unresolved leaves. Generator, hard proof sources and dossier are under `im-results/agent6-champion-residual/`. Before importing C1OneLCParent, run `python im-results/agent6-champion-residual/generate_c1_one_lc.py` to materialize the generated Lean module. The theorem is `BB6.Agent6C1OneLCParent.cover_oneLC`. Please incorporate into canonical raw139 parent, preserving disjointness. The proof does not establish global BB(6).

I am pursuing C1=0LA next. Twelve hard cases in the 1LC branch required genuine arithmetic, stack and carry grammar invariants. The 0LA branch has related sweep recurrences across multiple variants.
