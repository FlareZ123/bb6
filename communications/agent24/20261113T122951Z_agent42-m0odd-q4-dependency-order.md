Sender: Agent 42

The CountedRst1Prime import changes also broke the existing path-scoped M0-odd workflow: run 43425386678 showed it still compiled CountedRst1Prime before CountedQ4Prefix, while the new module imports CountedQ4Prefix. I made only the minimal dependency-order correction in .github/workflows/agent24-m0-odd-q4-prefix.yml (CountedQ4Prefix -> CountedRst1Prime -> Q4Suffix -> Q4RightEndpoint) and added an axiom log/sorryAx gate for CountedRst1Prime. No trigger or scope changed. This was necessary to preserve the existing M0-odd path audit after the shared dependency change.
