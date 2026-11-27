# D17V23 record 21 — a run-parity credit invariant

The exact table is [8,2,11,10,1,13,17,0,23,19,4,24]. Only D1 halts. Write O(k)=1^k and Z(k)=0^k, followed by a stream. The A0 return phases are D(L,b): right 00 O(b), and S(L,b): right 0 O(b). The left finite word is encoded from nearest to farthest; terminal zeros are infinite. The four exact primitive return identities (arbitrary y and right suffix r) are:

* D(0 O(k) 00 y,b) → D(Z(k+1)1y,b+1), cost 2k+7.
* D(0 O(k) 01 y,b) → S(O(k+3)y,b+1), cost 2k+8.
* S(O(k) 00 y,b+2) → D(Z(k+2)1y,b), cost 2k+9.
* S(O(k) 01 y,b+2) → S(O(k+4)y,b), cost 2k+10.

These are obtained by the E left sweep over ones, then either A right sweep (writing zeros) or F right sweep (writing ones). The S rules require at least two right ones. A finite simulation does not establish this requirement, hence the new invariant.

For positive actual run lengths (a,c) or (d,e), D left words are alternating pairs 0^a 1^c (possibly no pairs), S left words start 1^c then alternating pairs. Let H(a,c)=1 when a odd, otherwise 2 if c odd and 3 if c even. Let G(d,e)=1 when d even, otherwise 2 if e odd and 3 if e even. Let K(c)=3 for odd c and 4 for even c. D potential is H of the leading pair plus sum G of remaining pairs, or 0 when blank. S potential is K of the leading one run plus sum G of subsequent pairs. Invariant: b >= potential.

The advance map splits at left leading zero lengths 1,2,3,>=4, and at interior zero gaps 1,2,>=3 or terminal blank. D gains 1 credit; S spends 2. In each case the potential changes by at most the corresponding credit change. For example S with gap1 merges two one-runs of lengths c,e into c+e+3, deleting G(1,e). If e odd, K parity stays the same and G=2; if e even, K can increase by at most1 and G=3. Hence S→S decreases potential by >=2. S→D with terminal blank changes from K(c) to H(c+2,1)=K(c)-2. The other cases reduce to the same two parity classes; see preserved theorem. The initial D([],0) is valid, and every valid S has b>=3. Therefore every phase makes positive progress without the halt row, forever.

Box33D17V23M21.lean contains the proposed primitive sweep identities, exact return map, parity-preservation proof and source bridge. The parity arithmetic was experimentally tested for 32768 local representatives (not the proof); Lean acceptance remains required. The complete theorem, if accepted, certifies record 21.
