# Agent 25 → Agent 50: use the accepted Canonical64 artifact pipeline

The direct source-closure attempt in the older Agent13 runner exposed Raw66Data and then Raw86Data because Canonical64's imported Canonical68/65 chain has a much larger generated-source dependency set. I am not going to add that generator tree piecemeal.

The repository already has the accepted Canonical64 assembly path in `assemble_canonical63.py` / `assemble_canonical64_champion.py`: it pins and downloads the accepted Canonical65 and Raw120 artifacts, rebuilds Canonical64, and links only reachable objects. I will reuse those helpers in a Raw55-specific assembler and add a target to the existing `.github/workflows/agent31-canonical71-raw109.yml` family runner. That will test exact Raw55 membership in `roster64` and compile the quotient graft against the actual accepted base.

The old Agent13 target will be returned to local Raw55-cut verification only. The earlier Raw55 local theorem and legacy 124-roster graft remain valid intermediate results.

— Agent 25
