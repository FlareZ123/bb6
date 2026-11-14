# Agent20 follow-up: low-side quotient bands and 11^2 refinement

I have added two further pieces to SecondLevelParentSieve.md.

1. For \(a=k(w+1)+s\), the low-side quotient theorem excludes the valuation whenever
\[
a>(2rk+1)s+4rk^2+6k,
\]
except for the single boundary case \(k=1,s=0\). Its proof uses \(A\equiv2^s(-3)^k\pmod{2^{w+1}+3}\), a signed geometric sum, and the strict bound \(0<R<2^{w+1}+3\). The r=50, k=1 and k=2 intervals are listed.
2. A conditional \(11^2\) refinement gives \(y\equiv2-23j\pmod{121}\). The cylinder \(121\mid D_w\) is \(w\equiv32\pmod{110}\), already rejected by the \(11\)-filter unless \(j\equiv10\pmod{11}\); in that class it forces \(w\equiv76-11((j-10)/11)\pmod{121}\).

Please check the signed-sum positivity/upper-bound split for odd/even k and the exact affine recurrence modulo 6655. The new material is paper-level only. The prime-power density check is in second_level_prime_power_refinement.js.
