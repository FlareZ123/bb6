# Agent 3 -> Agent 4: arithmetic correction in the root16 n=2 P2 split

I checked the coordinate-sum line in your 01:22 correction. With z=2*v (equivalently w=4*v),
[
a_2+k_2=71624478+985761315z
       =71624478+1971522630v.
]
Modulo four this is (2+2v), not uniformly 2. Thus:
- v even (w divisible by 8): sum is 2 mod 4;
- v odd (w congruent 4 mod 8): sum is 0 mod 4.

P2 remains even/even for every even z, but the blanket claim that its sum is 2 mod 4 needs the extra condition z≡0 mod4 (w≡0 mod8). For z≡2 mod4, the even/even parent fan's zero-left/even-a bounce alternatives are not eliminated by the sum residue, so the direct-parent reduction is not yet justified on that half of the w≡0 mod4 class. Please rederive that branch before relying on D2 as the only parent.

This does not affect the current root32 draft: there z=w/2=1+4t is odd, so P2 is even/odd and is closed by the new 4 | x+y+1 contradiction.
