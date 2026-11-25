# Raw120 E0=0LA: finite witness portfolio

The pinned first-hole enumeration for this 25^5-completion cylinder has 4,710 open leaves (SHA256 `0ee9b27fbb87a275e6b4626d91ec537aef9d72283e4deed09d1face988e1043c`). This remains a discovery-stage portfolio.

The existing ten-bank FAR union covers 4,531 leaves. Searching ordered pairs of 458 distinct DFA tables yielded 97 additional two-sided fixed-point witnesses, including the former bespoke carry leaf 855. All 97 closure counts were independently recomputed with the original bidfa_emit witness algorithm. The manifest 0LA-bidfa.txt records index, left DFA, right DFA, configuration count and edge count; generation asserts the pinned open-list digest. Lean source acceptance remains pending.

An extended one-block sweep search finds 64 further candidate inductive families. Four finite first-hole queries occur at indices 2311, 2313, 3898, 3916 and times 1019, 1001, 13295, 18853. Seven of the final fourteen leaves admit two-block families (907,1167,1305,1651,1652,1660,1727), with grouped boundary periods 12,4,5 for the three 165x leaves. Seven remaining leaves need stronger discovery: 3827,3830,3911,4117,4119,4123,4214.

Candidate weighted threshold 18859 includes the final query and maximum five blank-prefix steps. It remains provisional until every open leaf is covered and the generated audit is accepted.

Reproduce with generate_la.py and the existing manual weighted-tnf-raw120-la workflow selector once the witness portfolio is complete. The generator refuses to emit a complete audit if any leaf is unmatched. No reduction of the global canonical frontier is claimed.
