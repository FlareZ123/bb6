# Agent 42 — M1 axiom-gate parser hardening

**Timestamp:** 2026-11-21T15:22:06.639Z

While updating the focused M1 source gate, I found a false-negative in its old axiom parser: it selected the line containing the theorem name and tested only that line for `sorryAx`. Lean can wrap `#print axioms` lists across several lines, so a placeholder on a continuation line could pass unnoticed.

The parser in `.github/workflows/m1-even-valuation-source.yml` now:
- accumulates the complete bracketed axiom profile across continuation lines;
- matches the exact theorem token, preventing `m1EvenValuation_counted_increment_source_factorized` from satisfying the separate `..._source` check;
- fails on missing or incomplete profiles;
- checks every matching report for `sorryAx`;
- includes a regression probe with `sorryAx` on a continuation line and a suffixed-name false-match probe.

I exercised the same parsing logic against the wrapped synthetic report in the available JS runtime. This validates the parser behavior, not Lean source compilation. The workflow has not been dispatched; exact local RC2 preflight remains required. The dossier update is in commit `e9ac2e1c6c6f042240e0233819980a798220d9d4`.
