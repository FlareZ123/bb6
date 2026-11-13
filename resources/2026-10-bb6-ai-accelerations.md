# BB(6) AI-discovered accelerations and holdouts (October 2026)

## Primary source

Marco Dos Santos, Vivek Veeriah, Alex Havrilla, Andrew Bolt, Goran Zuzic, Satinder Singh, and Tom Zahavy, **“At the Limits of Computability: Steps Towards Autonomous AI Discovery on the Busy Beaver Frontier”**, arXiv:2610.22603, 15 October 2026.

- Abstract: https://arxiv.org/abs/2610.22603
- Scope: automated discovery and Lean formalization of Collatz-like accelerations for Busy Beaver holdout machines.
- Reported BB(6) contribution: eleven holdouts receive newly discovered, formally verified Collatz-like transition systems; fifteen additional previously studied machines receive formal proofs of rules or new accelerations.
- The paper describes an initial BB(6) search space of about 1,000 holdouts (Table 2 gives 1,094), and reports 18 community-recognized cryptids in that domain at the time of the study.
- Crucial limitation: these accelerations reduce the machines' halting questions to arithmetic reachability questions; the paper explicitly leaves the eleven new machines' halting behavior unresolved and labels their cryptid status provisional pending community acceptance.

## Current public BB(6) status

The BusyBeaverWiki main page still lists only the lower bound `BB(6) > 2 ↑↑↑ 5`, with no exact value:

- https://wiki.bbchallenge.org/wiki/Main_Page

## Relevance to this repository

This paper is useful context for the global upper-bound/classification side of the BB(6) project: exact acceleration and formal verification do not by themselves classify a holdout as halting or non-halting. Any use of its machine list or transition systems should distinguish (1) formally verified acceleration, (2) arithmetic reachability still unresolved, and (3) an actual halting/non-halting classification. The paper does not establish an exact BB(6) value.
