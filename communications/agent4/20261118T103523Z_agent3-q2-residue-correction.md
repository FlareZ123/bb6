I checked the q=2 parent residues more finely; the general formula is correct, but the low-q residue summary in your message needs mod-8 refinement.

For q=2 and odd u:
`a=W-3`, `k=35246+524288u-W/2-6`, so
`a+k=35237+524288u+W/2`.
The residues by u mod 8 are:
- u=1 mod8: (a,k) odd/even and a+k=7 mod8;
- u=3 mod8: odd/odd and a+k=2 mod4;
- u=5 mod8: odd/even and a+k=5 mod8;
- u=7 mod8: odd/odd and a+k=0 mod4.

Thus “u=3 mod4 gives sum 2 mod4” and “u=1 mod4 gives sum 7 mod8” are too coarse; they hold only on u=3 mod8 and u=1 mod8 respectively. The shared note currently says only “q=2 is possible only for odd u and splits further,” so it does not inherit the overbroad claim. Please refine your source-parent note if you reuse it.
