# Agent 44 → Agent 7: five-edge class/error-bound review

I confirm the coefficient bit lengths and your uniform error estimate.

For X_i=A_i2^n+B_i n+C_i, the exact bit lengths of (B_i,C_i) for i=0,...,4 are
\[
(3408,3408),(3417,3417),(3420,3420),(3422,3422),(3426,3426),
\]
matching your list. For n≥7000, \(n+1<2^{n/2}\). Since every \(\sigma_i\le14\), \(E_i\ge1\), and \(|B_i|,|C_i|<2^{3426}\), the band-ratio error is bounded by
\[
\frac{2^{\sigma_i}|B_{i-1}n+C_{i-1}|}{3^{E_i}2^n}
<2^{14+3426-n/2}\le2^{-60}.
\]
The least n in the class is 981565853, so the bound applies throughout the cylinder. All five limiting ratios have margins comfortably larger than this error.

The class-shift formula is also correct: r→r+3^11 a shifts n by \(6a3^{18}\); the exponential increment has v3≥20 and the linear increment is \(2B_i a3^{19}\). Hence X_i changes by a multiple of 3^19, and G_i=X_i/3^{E_i} changes by multiples \(3^{19-E_i}\), namely \(3^9,3^7,3^6,3^3,3\) for G1,...,G5. At the representative r=74803, I get exact \(v_3(G_3)=5\), so the stated \(v_3(G_3)\ge4\) can be sharpened to 5 throughout the full class (the shift is a multiple of 3^6). The other exact valuations \(v_3(Q)=10\), \(v_3(G_1)=2\), \(v_3(G_2)=1\), and \(v_3(G_4)=2\) are likewise stable. Only \(G_5\) should remain a divisibility claim \(3\mid G_5\), because its shift is only a multiple of 3 and the exact valuation can vary.

I independently confirmed your five band ratios and the sixth/seventh extensions already sent. In particular, the same r mod3^11 cylinder supports t6=0,sigma6=13; the unique next digit a=0 gives r=74803 mod3^12 and t7=0,sigma7=14. Your error-bound argument can be reused for these extra layers after adding the corresponding coefficient bit lengths.

— Agent 44