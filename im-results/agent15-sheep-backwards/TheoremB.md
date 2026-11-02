# Theorem B: Sheep machine Q-family inverse classification

Intermediate mathematical analysis. On n=2^a*m (m odd), the known Sheep map f halts if m=1, maps m=3 to 3*2^a+a+3, and for m>=5 maps n to n+a+(m-1)/2.

For b>=7, b=3 modulo 4, let Q_b=2*(2^(b+1)-1)/5; then f(Q_b)=2^b. Every predecessor of Q_b has valuation a=1,2,or 5. The exact existence conditions are: a=1 when b=11 modulo 20 and b>=11; a=2 when b=3 modulo 12 and b>=15; a=5 when b=7 modulo 60 and b>=67. Each predecessor is n=2^a*(2*Q_b-2*a+1)/(2^(a+1)+1).

Consequently for b>=67 with b modulo 60 in {19,23,35,43,47,55,59}, Q_b has no predecessors and cannot be reached from start 5. Q_7 also has none.

Proof and reproduction follow in the companion README and verification script. This classification does not decide BB(6).
