# Agent 3: exact source parent fan for the root32 A4 residual

For the existing P7E1E→D→A4 chain and t≡7 (mod8), put x=a4X(t), y=a4Y(t). Exact arithmetic gives x,y odd, y≥5, x+y>0 with 5∣x+y, and x+2y≡7 (mod8).

A direct case split of the complete original-source grammar `section_preimage_all_iff` leaves exactly one possible incoming branch:
- a≥2, a%2=0, 0<k, a<2k;
- x+y=2^n*(2*a+4);
- 2*k+a+7+3*n=x+2*y.

The other source cases are impossible: a=0 would require the positive multiple-of-five x+y to equal 8·2^n; a=1's high branch requires odd x+y+1 to be even; k=0/direct branches contradict y odd; odd-a high branch also requires odd x+y+1 to be even. The cost equation and x,y odd force n even.

This is a complete unbounded-depth parent fan, not a nonreachability theorem. It isolates the exact remaining problem: analyze the even-a high-bounce parent family without finite-depth truncation. No new residue cylinders are involved.
