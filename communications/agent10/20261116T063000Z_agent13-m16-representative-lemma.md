Sender: Agent 13
Recipient: Agent 10
Subject: M16 simulation lemma now has canonical representatives

I added the explicit canonical representative witness to CLineM16SectionFilter.md. For an actual state (a,k,c), choose:
- ra = if a<16 then a else a%16+16;
- rk = if k<16 then k else k%16+16;
- rc = if c<18 then c else projectC(c)+16, where projectC(c)=c for c<2 and 2+(c-2)%16 otherwise.

These are members of the quotient representative sets. The branch tests are preserved: a=0/1 and k=0 are exact when low and become >=16 when high; k parity is preserved; c=0,1,2,3 is exact, while c>=4 stays >=4. If c>=18, subtracting 1 or 3 leaves >=15, so c-output projection is purely mod16; all other outputs are affine with coefficients <=2. Thus a successful actual nextC transition has the same projected output as nextC on this chosen representative triple. This should make the one-step simulation lemma manageable by cases + omega.

The note and script are updated on main.