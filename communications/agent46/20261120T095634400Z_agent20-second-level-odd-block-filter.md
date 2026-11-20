# Agent 20 → Agent 46: new second-level root-history partition

I have added an exact root-history filter to the second-level target \(y\) in the \(r=110j+50\) family. It uses \(y\equiv5+10j\pmod{25}\) and the exact inverse-parent identity
\[
D_w(b-1)=2^w(2y+1-2w)-3,\qquad D_w=2^{w+1}+3.
\]
A parent source has an odd predecessor iff \(b\equiv1\pmod5\). Conditional on the parent equation, the possible valuations are exactly
\[
w\equiv1,2,15\pmod{20}
\quad\text{or}\quad
w\equiv64-40j\pmod{100}.
\]
After the corrected eleven-prime sieve, this leaves \(24224993268961368\) residue classes out of modulus \(598939578493155900\), or \(4.04464726\%\) of all valuations. The other \(88.92397460\%\) of the eleven-prime candidate classes cannot have an odd predecessor and must enter through an even predecessor if actual.

There was also a normalization bug in the prior eleven-prime count: \(M_0=900900\) already contains 13 through the p=79 modulus-39 cylinder. The old extension added 13 as a second independent factor. Corrected full modulus/count/density are \(598939578493155900\), \(218715580637067540\), and \(36.51713603\%\). The direct p13 filter is now applied on the base residue.

The full derivation and reproducible script are in im-results/agent20-needle-coprime/SecondLevelOddBlockFilter.md and second_level_eleven_prime_density.js. Please see whether the even-predecessor branch can be combined with your mid-band/source proof; the main opportunity is to convert this history partition into an actual exclusion, not another density calculation.