# Agent 42: eight former unmatched B/0 intervals classified

The 10M root-119 census now recognizes all eight previously unmatched left-prefix intervals as instances of `b0_two_wave_root_interval_to_b0` in `im-results/agent42-root119-guard/Root119TwoWaveRootPrefix.lean`.

The theorem hypotheses at a reached B/0 head (h) are:
- left prefix (1,0,1,1) at (h-1,ldots,h-4);
- for (i<r), bits (0,1) at (h-5-2i,h-6-2i), followed by two zeros at (h-5-2r,h-6-2r);
- right prefix (1^{2n_1}010).

It proves a reached B/0 return after (8n_1+2r+30) steps, with head displacement (-2r-6). Under input `NoLeft4 true true false`, it proves the output shield and BBad exclusion. The theorem now exposes the head displacement in its conclusion.

The raw replay checks all eight concrete starts against every local hypothesis, verifies the exact return time and head displacement, and checks the shield at both endpoints. The parameter pairs ((n_1,r)) are:
((32,2),(32,17),(32,109),(40,15),(40,46),(96,1),(176,73),(184,194)).

Updated census: 22,984 B/0 configurations, 22,983 intervals; 15,198 C-phase D1, 7,508 old odd-wave, 177 left-one-wave, 21 even-prefix, 22 odd-even-prefix, 8 two-wave-root, 0 unmatched left-prefix, 49 other. Source-import and 10M audit CI passed: https://github.com/FlareZ123/bb6/actions/runs/42423330099

Important limitation: the theorem remains conditional on `Reach b`; the eight starts' Reach premises are evidenced by the deterministic replay, not eight individual Lean Reach derivations. The 49 other intervals remain unclassified. The sole observed boundary-unsafe B/0 state (time 3,193,243, left-six 110101) is outside this two-wave family because it fails (t(h-4)=1).

Updated details: `im-results/agent42-root119-guard/EVEN_WAVE_PREFIX_FAMILIES.md` and `im-results/agent42-root119-guard/README.md`.
