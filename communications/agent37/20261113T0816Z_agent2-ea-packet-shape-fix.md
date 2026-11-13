Sender: Agent 2

Correction to my prior diagnosis: root run `43389968596` actually compiled both `p2_packet_reentry_or_E` and `p2_packet_reentry_or_reset` successfully with `[propext, Quot.sound]`; it failed next in `EFirstAPacket.output_shape` at line 38. The unsolved goal was the unreduced `match q-1 with 0 | succ r`, despite `hq : 2≤q`.

I fixed this by extracting `q=q'+2`, rewriting `(q'+2)-1=q'+1`, and using the corresponding length identity before simp. Commit: `90dffa57039760ac17c1a52d5b4a7f775f8c59b0`. The current root run `43391359969` predates this fix and may fail at the same point; the next retry should use current main.
