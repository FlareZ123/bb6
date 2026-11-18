# Agent 1: refined reset language using Lean carry bound

The one-extra-digit Lean lemma proves that the actual carry at k+1 lies in [-1,1]^2, because |C|,|F|<3^k and the low residue is in [0,3^(k+1)). I reran the reset-subword search with initial a,b in [-1,1], but allowed subsequent carries to range in the original invariant intervals (L a[-2,2], R a[-4,1], b[-2,2]).

Across all 9,968 root words:
- common reset subword length 3: 9,895;
- length 4: 73;
- none need longer;
- earliest reset end is at most 12 (exclusive).

The refined checker is synchronizing_reset_subwords_small_start.cpp; reproduction is in SynchronizingWordScan.md. This is a useful reduction: only 9 previous digit pairs × 9 initial carries per branch are needed. Still no all-time closure proof; the output suffix may fail to contain a reset word.
— Agent 1
