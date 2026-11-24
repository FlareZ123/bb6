# Signed q0 graph: aperiodicity and repeated-word obstruction

## Established theorem

Every infinite strict-interior integer path in the exact signed q0 graph has an aperiodic digit itinerary, including the absence of an eventually periodic tail. Every interior vertex has at most one interior predecessor across the four digit types. These results concern the reduced signed graph of [Q0MacroReduction](Q0MacroReduction.md); they do not exclude all finite paths of the required length or decide the original machine.

Q0SlopePacking.lean proves interior_predecessor_unique, slope_packing and simple_slope_cycle; Q0Aperiodic.lean proves no_periodic_interior and no_eventually_periodic_interior. Lean 4.36.0-rc2 compiled both locally against verbatim extracted relevant declarations of Q0MacroCore. The exported axioms are standard [propext, Classical.choice, Quot.sound] or subsets; small_check uses kernel decide and has no axioms. Full original-file source CI was not run.

## Proof

Write the exact edge as p'=p+l_d, 16y'=y+d*p+c_d, with (d,l_d,c_d)=(0,3,0),(1,5,6),(4,4,18),(5,6,32). Strict interior means y>0 and 3y<p. Suppose an infinite path has least positive digit period k and total cost L. Then p_{i+k}=p_i+L. Integer differences t_i=y_{i+k}-y_i satisfy 16t_{i+1}=t_i+d_i L. Their k-shift differences contract by exactly 16 and hence vanish by unlimited integer divisibility. Thus t_i is k-periodic. Applying periodic nonnegativity to t_i and L-3t_i proves 0<=3t_i<=L.

The reverse slope step is unique: t_i is the remainder of 16t_{i+1} modulo L and d_i its quotient. A repeated slope in one period forces a shorter digit period by backward propagation and periodic extension. The k distinct slopes lie in four intervals [dL/16,dL/16+L/48], each containing at most floor(L/48)+1 integers. Unless every digit is five, L<6k. Hence k<=4(floor(L/48)+1)<=k/2+4, so k<=8 and L<48, whence k<=4. For lengths 1..4, kernel enumeration of (16^k-1) | L*D with D=sum d_i16^i leaves constant zero, constant five and the length-three all-one word. The latter has identical slope 1 at every position and is nonprimitive. Only primitive zero or five remain. A zero tail divides y by 16 forever; a five tail divides p-3y by 16 forever. Both contradict strict interior.

## Finite repetition bound (paper derivation)

Let a primitive nonempty word of length k occur r>=2 consecutive times in a finite strict-interior path, terminal rank P. Set B=16^k, M=B-1, L=sum costs, D=sum d_i16^i, and C the composed intercept. At block boundaries p_j=p_0+jL and B*y_{j+1}=y_j+D*p_j+C. Differences delta_j=y_{j+1}-y_j obey B*delta_{j+1}=delta_j+D*L. Set A_j=M*delta_j-D*L. Then A_0=B^(r-1)*A_{r-1}.

A_0 cannot vanish: if it did, delta_1=delta_0, and the difference between two copies forms the same cyclic slope system. Its initial slope lies between 0 and L/3 because delta_0=D*L/M and 0<=D<=M/3. Reverse uniqueness and primitivity give distinct slopes. The packing theorem forces a constant zero or five word. Equal differences then force y=0 or p-3y=0 respectively, contradicting strict interior.

Therefore B^(r-1)<=|A_0|<=M*(P+L)/3<B*P (since |delta_0|<=P/3, D<=M/3 and L<=P). In particular 16^(k*(r-2))<P. A primitive cube with 16^k>=P is impossible. For a nonprimitive word use its primitive root and multiply the repetition count. The finite bound itself is a paper proof; its slope obstruction is kernel checked.

## Open obligation

The authentic q0 reduction needs exclusion of every path of length 8u+5 from (24u+22,6u+4). Aperiodicity alone does not imply a finite bound. Reverse uniqueness permits exact rank-crossing tests without inverse branching; seek an all-parameter barrier rather than increasing fixed parameter cutoffs.
