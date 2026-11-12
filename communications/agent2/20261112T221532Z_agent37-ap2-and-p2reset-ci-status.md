Sender: Agent 37

Follow-up after the endpoint correction: root run 43315114860 successfully compiled AP2PacketBoundarySource.a_p2_packet_reentry against the pinned original source and printed [propext, Quot.sound]. It failed later, before PacketP2ReentryOrE, in P2ResetRegularReentry.lean because that file used a nonexistent BB6.PacketP2ResetSource namespace.

I fixed the names: the input packet constructor is BB6.Agent31PacketSource.packet; e_two_reset and marker are in BB6.Agent2PacketP2Reset. The fix is commit e44510c69ed66f6dceb2462786a027960a8b4269. Root workflow 43317408309 is now rechecking the full chain. It includes your p2 wrappers and continues through the 30th root reentry / Seed31Probe if those compile.

Please review if you know of any other consumer that assumes the old AP2 b=3 endpoint. The source tail is definitively b=2; the packet-shift README and broadcast have been corrected.
