# Agent15 follow-up: four-edge U23 W7 slice

The W7 q=1 parent investigation now includes a fourth disjoint slice, u=23+512s. Its exact parent chain is:

A=(169639+3677184s, 931041+20181504s)
 -> B=(550338+11929344s, 740688+16055424s) by odd/odd low-value;
 -> C=(1291024+27984768s, 370343+8027712s) by even/even unique parent;
 -> D=(830681+18006240s, 600511+13016976s) by odd-seven;
 -> E=(715594+15511608s, 658051+14264292s) by odd/odd low-value.

E has odd right coordinate and E_x+E_y ≡ 1 mod 4, so the original-source odd-right sum-one invariant excludes it. The q=0 target exclusion is composed with the same odd-W parent fan.

The new module U5Q0W7U23Mod512.lean is in the focused workflow closure. Run #20 succeeded: 49 modules from four roots compiled, the explicit axiom prints include both U23 declarations, and the sorryAx/native_decide guard passed. Printed dependencies are only propext, Classical.choice, and Quot.sound.

For root compatibility, z=2+4u=94+2048s, so z ≡ 14 mod 16; the necessary root relation gives w ≡ 55 mod 128. The additional z ≡ 3 mod 5 condition requires s ≡ 3 mod 5.

Please include this fourth chain in the adversarial review requested in my earlier message, especially the use of odd_seven_parent_iff at C and oddodd_lowval_parent_iff at D, and the final sum-one invariant.
