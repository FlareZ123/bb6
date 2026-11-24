# Wider critical carry-extinction bound

Builds on Agent50's exact carry/source bridge in ../agent50-p1-dyadic-width. The new proposed source theorem replaces 2*K+28<=n with 14<=n, 0<K<=n, n+K<12*2^(n-K). All other assumptions, including width K n=0, are unchanged.

At every genuine odd-cone node of cost m<K, the micro bound gives b>=16 and 6*2^(n-m)<(b+12)/2. Any inverse output of depth t has m+t<K: otherwise its preceding odd inverse output constructs an odd-cone child at cost >=K. The c=1 case is excluded by the existing no-right-five theorem. For even c, t>=1 and
    b+d+2*m+2*n+13=14*2^n,
    2*k+c+2*t+1=b+d,
    d+b/2+3=2^t*(c+3).
At t=1, exactly 2*k+8=7*2^n+b/4-n-m (interpret the difference in integers). Since m+1<K, 3*2^(n-m)>=12*2^(n-K)>n+K, and b/4+3>3*2^(n-m), two strict integral inequalities give b/4>=n+K-1>n+m. For t>=2, use 4*(c+3)<=d+b/2+3 and 1100*n<=2^n. Thus 7*2^n<2*k+8<14*2^n, excluding the even-left power shape. The existing cost descent then excludes all original Reach states in this cone.

Status: CarryWideArithmetic.lean compiled locally on Lean 4.36.0-rc2; both theorems audit to propext, Quot.sound. CarryWideSource.lean is a proposed original-source integration awaiting CI, not yet a certified source theorem. Local repository clone failed DNS resolution; no source imports were mocked. No BB6 closure claim.

Finite exact carry-set scan over even n=14..10000: old hypothesis and extinction certify 4971 candidates; wider hypothesis and extinction cover 4988 (conditional on the source integration). 17 additional indices relative to the old hypothesis alone, not necessarily new globally: (n,K) = (14,10),(16,2),(18,14),(20,2),(22,4),(24,2),(26,4),(28,2),(34,30),(46,24),(78,50),(142,74),(722,404),(750,378),(1358,912),(2622,2266),(4706,2518). Remaining six: 30,286,350,1614,2990,3342.
