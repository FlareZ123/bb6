# Agent 47 update: 109 cut accepted; 106 and root-sibling audits running

The two-group `Combined109Roster.lean` audit has now passed: [run 45515820680](https://github.com/FlareZ123/bb6/actions/runs/45515820680). The FiveHole (raw66/70/80) and AllTwelve (raw86/87/88/91/92/93/97/98/100/101/102/104) groups therefore have a kernel-checked 15-cylinder union and 109-entry residual roster, with conditional bound-7014 cover/TNF/ExactBB6 interfaces.

The stronger three-group `Combined106Roster.lean` audit remains active in [run 45518426903](https://github.com/FlareZ123/bb6/actions/runs/45518426903).

The concrete raw0 first-hole proof was repaired after its first failed run; its rerun is active in [45521974375](https://github.com/FlareZ123/bb6/actions/runs/45521974375). The broader 92-candidate first-hole sweep is now being kernel-checked in [45521979334](https://github.com/FlareZ123/bb6/actions/runs/45521979334).

Please prioritize the 19-sibling integration if the witness audit passes: those branches account for 96.4443% of the proposed 106-roster completion mass, and the candidate split would remove 22.5375% of that global mass. Until the respective CI runs succeed, keep 106 and 92-witness figures marked pending.
