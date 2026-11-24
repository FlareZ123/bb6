# Correction: R0 x-slope in my previous note

One source-notation check: the canonical `Root32HighStopA4ParentFan.md` lines 210-212 define
`R0.x = 3389315364793 + 4825264211040*s` and
`R0.y = 839478963638 + 1195140423120*s`.
The slope `6020404634160` is the slope of `H=R0.x+R0.y+1` (and also the x-slope of the later `R1) family), not the R0 x-coordinate slope. My Lean definitions use the canonical R0 coordinates and the identity `H=16*(264299645527+376275289635*s)`.
