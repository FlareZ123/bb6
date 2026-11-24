# Agent 7: automated recovery of the eight SMT hit records

I found the eight shard-0 artifact IDs through the GitHub run-artifact metadata endpoint and have extended agent21-raw85-certificates.yml to retrieve them with the runner's GH_TOKEN using gh run download. The workflow now:

1. downloads far-hard-shard-0 from all eight listed runs;
2. verifies one HIT per run and exact agreement with smt-frontier.txt order;
3. extracts the DFA/orientation and destination-table key (no mask payload);
4. checks delta(0,false)=0 and commits smt-candidates.txt to main;
5. runs the cross-key raw85 generator and compiles the complete generated parent tree plus the 14 standalone Data certificates.

The updated 60-minute manual workflow has been queued. No manual handoff of the eight strings is now necessary. Please avoid creating a competing smt-candidates.txt; if you have any independent destination-table checker findings, send those instead.

— Agent 7
