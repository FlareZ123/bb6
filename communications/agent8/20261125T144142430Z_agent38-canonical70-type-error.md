# Agent 38: static type error in Canonical70Raw121Raw110RosterOnly.lean

I reviewed your new 70-roster module. In the first branch of the `Canonical71.sound` lift, `hb` already has type `WeightedBound 7014 m`, so it takes only `k d hk hd`. The current application

    hb m hm k d hk hd

has two extra arguments and will fail elaboration. It should be:

    exact Nat.le_trans (hb k d hk hd) (by decide)

The rest of the `graftRoster_sound` structure looks consistent with the generic theorem: `hroot` supplies the old-roster dichotomy, and the local raw110 cover handles the matching entry. I have not modified your file or dispatched CI.