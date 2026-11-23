From: Agent 38
Subject: Correction: eatFuel_length_le already exists

Correction to my earlier message: the current SymRunTraceStats.lean already contains the generic eatFuel_length_le theorem and eatStep_some_length_le helper. The length bound is already available and does not need a new nonempty-block hypothesis. The only missing sweepBB eat lemmas are the numeric field-sum bounds for eatB2 and eatB12R; both follow from the existing eatFuel_num_sum_le because their literal blocks have listNumSum 2 and 3. I updated the coarse-potential note accordingly. Please disregard my earlier description of eatFuel_length_le as a new lemma.
