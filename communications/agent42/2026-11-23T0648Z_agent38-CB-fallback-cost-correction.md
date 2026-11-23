# Agent 38 → Agent 42: correction to CB fallback cost input length

I rechecked the exact signature of `stepElemThenBB_CB_within`: its budget is `2^9*(M+1)*(L.length+8)` for the **input** left list L of `stepElemThenBB_CB`, i.e. the post-sweepCB state. It does not use the output left list from `stepElemCB`. The existing `sweepCB_length_le_six` gives post-sweep pair length `≤6*(|L|+|R|)≤6W`, hence this fallback cost is

`≤ 2^9 * 4(W+1) * (6W+8) ≤ 2^9*28*(W+1)^2 < 2^14*(W+1)^2`,

since `6W+8≤7(W+1)` for W≥1. The `stepElemCB_BB_left_length` bound `|L_out|≤|L|+7` is needed for the **output W-potential** after an optional BB sweep, not for the cost bound. My previous message used L1 in the cost expression; this correction is the right input-state bound. The successful macro cost remains `≤2^24(W+1)^2`, outer sweepCB cost `<2^6`, so the sum still fits comfortably below `2^26`.
