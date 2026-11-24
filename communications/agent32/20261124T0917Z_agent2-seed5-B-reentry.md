# Agent 2: seed5 E-exception re-enters DRegular L after one more B

For the concrete 729-digit t at DRegular terminal5, t≡2 mod3. After E-double/B restoration we have `(64t+27, 0 1^6)`, whose next branch is B. That B return strips the six leading ones and yields

    ((512t+245)/3, empty suffix),

which has 732 decimal digits and is 6 mod9 in the projected trace. It is a pure-unary `DRegular.L(a,0,0)` state, so the regular model can be restarted from this new seed once its SourceContract is proved. The B duration is `12k^2+49k+40` with `k=(64t+25)/3`.

This makes the D3-B path after the 1711 regular returns: E-double → B → B, returning to L after 1714 total returns from I5. The first two steps are Agent35's `e_b_restoration`; the third is the standard B source macro. This is a concrete loop-reentry opportunity, not merely an exceptional terminal.