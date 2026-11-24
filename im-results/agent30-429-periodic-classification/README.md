# Arbitrary-period escape-corridor classification for #429

Local Lean 4.36.0-rc2 kernel checked with exact accelerator declarations and standard axioms only. Full unchanged-module CI pending.

Theorem BB429.PeriodicHigh.ultimately_periodic_enters_ray (BB429PeriodicSource.lean): every infinite successful BB429.next trajectory whose branch tags are ultimately periodic has a state (u,u+8) with u>=17 and u=1 mod4. Tags distinguish F,S,E and coalesce resets. This proves necessity of Agent6's known four-step escape corridor for arbitrary ultimately periodic itineraries.

Put A=2u+6,R=2u+w. Ordinary steps F,S,E update (A,R) to (2A,R+3),(2A-R+9,R+11),(2A-R+1,R+7). At odd rank, two-step ordinary blocks have second step F. Binary e=0 for FF, e=1 for EF or SF. Then A'=4A-2eR+c, R'=R+delta, with (c,delta)=(0,6),(2,10),(18,14). Rank mod4 alternates.

A primitive mixed period l has labeled period L=l if even and 2l otherwise. Its rank drift 4m satisfies 2m<=7l for even l and m=3(l+h) for odd l (h exceptional blocks). D_n=A_(n+L)-A_n obeys D_(n+1)=4D_n-8m e_n. D_(n+l)-D_n grows by factor4 but is linearly bounded, so vanishes. D is l-periodic, divisible by4. Even integer p=D/4 satisfies p_(n+1)=4p_n-2m e_n. Mixed periodicity forces 0<p<2m/3; e0 forces p<m/6 and e1 forces p>m/2. All primitive phases have distinct p (equal p forces equal future digits). Counting even integers yields 6l<m+6 and 12h<m+12. Even l forces l=2,m=7, no low numerator. Odd l forces l=3,h=2,13<=m<=15, at most one high numerator. Contradiction.

All e0 impossible by geometric growth. All e1 yields 3A-2R=2 or -6 from the two-block affine recurrence, hence the corridor. A periodic reset would bound u at every repeat by 22*2^P, but rank grows unboundedly and eventually forces F at that phase.

The five Lean modules cover source coordinates and counting, mixed-cycle obstruction, affine difference dynamics, primitive-period reduction and corridor, and the final tagged source trajectory. No blank-root entry or BB(6) bound claimed. Reverse signed inverse groundwork is present but no full reverse theorem yet.
