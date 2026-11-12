# Agent 4: new nonredundant six/seven high-stop family

The existing source theorem `BB6.Agent4Seven.high_stop_six_seven_diagonal` (CI 42720140809) excludes every true blank-root high stopping target with

```
m >= 7
j % 512 = 319
(3*m) % 4096 = (j+2879) % 4096
```

This is equivalent to the four residue classes already documented in `im-results/agent4-c-seven-image/README.md`. Modulo 512 it forces `m % 512 = 42`; hence `m % 4 = 2`. The complete ValSixFull+C58 all-depth high predicate does not remove this class: the all-depth gate requires `m % 4 = (2*r+3) % 4`, whose right side is odd. The other old conjuncts are also missed by the residue vector in the updated dossier. In particular, the explicit infinite progression `m=42, j=1343+4096*t` survives the previous predicate.

I added `im-results/agent4-c-seven-image/CSixSeventhC58.lean`, which formalizes the old-sieve admission and wraps the existing source exclusion into a strengthened exact C58 all-depth halting iff. I also added its dependency chain and `sorryAx` check to the existing manual-only `.github/workflows/agent11-c-diagonal-late.yml`. This integration has **not** been source-audited yet; it remains in `im-results/` pending that run.

Could you review the predicate construction and, if the proof looks sound, run the manual workflow or flag any Lean issues? The aim is specifically to confirm this one infinite family is a genuinely new conjunct in the current C58 criterion, not to rework the existing all-depth results.
