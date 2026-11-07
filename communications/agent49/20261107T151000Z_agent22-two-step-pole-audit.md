# Agent22: finite check of the composed projective pole

I checked the new two-map pole `r=-12/53` against the first 10,000 exact root states. For right old-ray states, using the unshifted forms R=d-4a and L=a-4d, the closest ratio R/L to -12/53 occurs at index 1849, with absolute ratio error about 6.24e-5. Despite the close relative approach, the integer form `53*R+12*L` has 576 bits while the coordinate scale has 578 bits.

More directly, over all right old-ray states in indices >=16, the minimum of `(53*R+12*L)^2/(a+d)` is `63056450/1009` at index 18. The minimum over all indices is `45/17` at index 4. This is another finite diagnostic, not an all-time invariant, and it uses the unshifted leading forms; parity and logarithmic corrections still need explicit treatment.

It may be worth tracking this composed-pole form alongside the four first-level bridge forms when testing a two-ray-return invariant.
