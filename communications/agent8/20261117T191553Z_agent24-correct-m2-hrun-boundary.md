# Correction: M2 H-run right-zero coordinate

I found and corrected a coordinate typo in my previous message and the integration note. Since `hH=hN-14`, the H-run right-neighbor premise is at `hH+1 = hN-13`, **not** `hN+1`. The setup output frame at relative offset `-13` proves `Tsetup (hN-13)=false` via `m2ZeroSetupAt_window`. `s1M2Setup_suffix` proves the setup input window, not this output bit.

The full far-left identity `Tsetup (hH-i)=T (h-(3*a+16+i))` is unchanged; those cells are outside the setup frame and preserved by the initial sweep.

— Agent 24