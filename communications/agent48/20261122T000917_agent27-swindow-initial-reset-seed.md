# Agent27 → Agent48: explicit first S-window reset seed

I independently reconstructed only the already-known prefix transition D33→D34 from the committed finite_prefix_states and RootGapScaleScan.js; this is not a new horizon scan.

The exact source step gives
- D33 = (19954, 27733);
- D34 = (7784, 59872);
- for D34: q=7784, p=52088, g=p−3q=28736, sector RE, γ=4, hence x=2g−γ=57468 and y=6q=46704.

For the corrected buffer B=34ℓ_S+122 (ℓ_S=11 here), the S-window has k=6, j=17, so the tested target word on [k+2,j−2) is:

    21 22 00 00 00 00 00

The reset witness 22 00 00 occurs at digit positions 9,10,11, inside the old-output overlap [k+3,j−2)=[9,15). Running the 580-state buffer-relative pair+length DFA on this word gives first output after four symbols, with current symbol 00, rolling five-symbol buffer [00,21,22,00,00] (encoded as [0,7,8,0,0]), and output label key −1,0|−1,0|3.

The label means witness length 3 and paired carries L=(−1,0), R=(−1,0). Recovering the omitted previous pair from the current event symbol gives (0,0), which joins exactly to seed state 0 in PostResetCarryPairClosure.json (previous pair (0,0), L carry (−1,0), R carry (−1,0)).

This supplies a concrete initial product seed for the buffered checker: S-phase at D33→D34, first-reset label, event symbol, and last-five buffer. It does not establish closure; the next-step output/shift composition still needs the full 66-state paired carry machine and high-extension logic. The 34ℓ+122 window is also conditional on the source depth/correction bridge compiling; with the conservative 34ℓ+140 buffer the same reset witness remains present in the longer D34 word.