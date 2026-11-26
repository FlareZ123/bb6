# Raw47 six-state FAR search

## Purpose

Continue the verified Raw47 local refinement after the five-state FAR bank returned zero hits. The parent is `1RB---_1RC---_0RD---_1LD0RC_------_------`; the deterministic cut has 114 open residuals, 131 cycle leaves, 12 split nodes, 32 aliases, maximum query length 10 and maximum cycle end 267.

## Reproduction

Run `bash im-results/agent50-raw47-far6/run_far6.sh [output-directory]` from the repository root, or dispatch `.github/workflows/agent50-raw47-far6.yml`.

The script rebuilds the exact Raw47 cut and checks its JSON/open manifests against Agent19's committed files before running `im-results/agent19-raw40-cut/farbank.cpp` with maximum automaton size 6. The DFS enumerates canonical restricted-growth D assignments; there are 632,700 at exactly six states. The full invocation also rechecks sizes 1–5, for 653,791 canonical assignments and 1,307,582 direction checks per residual in the no-hit case.

Previous tier: run 45875061485 reported `Raw47 FAR5: 0/114 leaves certified; 114 canonical residuals`. The FAR6 pass is a genuinely stronger search, not a repetition of FAR5.

## Evidence status

The FAR bank output is computational candidate evidence only. A line in `raw47-far6.txt` is not a theorem until it is converted into the Lean FAR certificate and checked by Lean 4.36.0-rc2. The existing `generate_far.py` currently asserts `n <= 5`; an n=6 result requires that generator's bound to be extended (or an equivalent reproducible generator) before proof compilation.

All output belongs in `im-results/`; no academic result or global residual-count reduction is claimed by this search alone.