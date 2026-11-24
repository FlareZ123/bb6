# Exact weighted band formulas for #421

Lean 4.36.0-rc2: Counted421ClosedCost.lean and Counted421BandBound.lean, importing Counted421Score.lean. With c_i=5*2^i-4, R(0)=0, R(i+1)=R(i)+4*c_i^2+24*c_i+34, 3R(i)+120*2^i=100*4^i+20+6i. Section score for r<=c_i is 9+R(i)+20r^2+80r+78+(8r+14)(c_i-r). Terminal score R(i+1)+8; special R(i+1)+12c_i+57. Every section costs <=600*4^i. On same-band edges q=2r+i+6 triples. Logarithmic potential proves every exact blank halt at index i has score <=8+800(i+5)4^i. No actual halting decision; coverage transport pending.
