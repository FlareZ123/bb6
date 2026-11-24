# Holdout #688: exact exponential stopping diagonal and density-zero inverse obstruction

**Theorems.** For the pinned six-state #688 acceleration from the authentic blank root, halting is equivalent to reaching the odd-phase diagonal (x,y)=(X_j,X_j), where X_j=4^(j+1)-j-1, j is a positive odd integer. Every even index is excluded. For every epsilon>0 there is a fixed binary residue modulus and a finite exceptional initial interval such that the remaining *reachable* stopping-diagonal indices belong to fewer than epsilon times the modulus residue classes. Hence the set of reachable candidate indices has upper natural density zero. The latter is an all-parameter mathematical proof, not an inference from simulations or a whole-machine decision.

The complete arithmetic halt equivalence, even-index exclusion, large-parent law, local binary ray arithmetic, collision identity and affine coefficient theorem are kernel-accepted locally with standard axioms only. The density proof is a paper proof using those lemmas. The exact arithmetic transcription uses the pinned [upstream acceleration](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/M_1RB1RF_1LC1LF_0RE1LD_0LB1LD_HHH1RC_1RA0RD.lean), whose isHalt_iff_acceleration is the external source certificate; the simultaneous source import has not been compiled here.

## 1. Exact two-counter collapse

In the upstream E(a,b,c) family, start E(0,0,2). From a=0, take k=min(b,floor(c/2)) ordinary steps E(a,b,c) -> E(a+2,b-1,c-2), followed by one non-drain step. Put l=b-k, r=c-2k, K=(5,3,9,7,12,10). The resulting next return (B,C) is

* l=0, r=6: halt;
* l=0, r<6: (0,4k+K[r]);
* l=0, r>=7: (2k+4,r-6), called H;
* l=1: (2,4k+3-2r);
* l>=2: (l-2,4k+7-2r), called L.

When l>0, r is 0 or 1. Each macro consists of exactly k+1 original accelerated queries, last one undefined only in the halt case. Lean Collapse.halt_iff proves both directions of finite termination (not just simulation soundness).

## 2. Even excursions and exact stopping diagonal

An even output can occur only on H from an even input, boundary r=4 from even input, or r=5 from odd input. Every even excursion starts at (0,c0), where c0=2 initially, c0=16*2^i-4 after a boundary-4 reset (since b+4=4*2^i), or c0=4b+10 after a boundary-5 reset from (b,2b+5). After t consecutive H transitions the exact formulas are

    b+4=4*2^t,
    c+8*2^t=c0+8+2t.

Terminal condition c=2b+6 is equivalent to c0+2t+10=16*2^t. It is impossible for c0=2, or c0=16*2^i-4: the latter would give 16(2^t-2^i)=2t+6, impossible if t<=i, and at least 16*2^(t-1)>2t+6 if t>i.

For c0=4b+10 the condition forces t even, t=2j, and x=b+4=4*2^(2j)-j-1=X_j, j>=1. Conversely every such reached boundary-5 state halts: the H guard is true at every intermediate i<t because c-2b=16(2^t-2^i)-2(t-i)+6>=20, using 2^t-2^i>=t-i. At i=t the exact terminal gate holds. Lean Root.root_halt_iff checks all of this, including actual reachability from root and both implications.

## 3. Odd coordinates and complete large-target parent alternatives

When c odd, put x=b+4, y=(c+3)/2, with x>=4,y>=2. The regular steps are

    H: x<y    -> (2x,y-x+1)
    L: x>=y+4 -> (x-y,2y).

The other odd cases have x-y=3,2,1,0 and enter either an odd state x'=6/4/4 or the even phase. For a reachable odd target (x,y) with both coordinates >=7, the parent is therefore one of

    H inverse: (x/2,y+x/2-1), if x even;
    L inverse: (x+y/2,y/2),   if y even;
    even feeder: 2x+y=8*2^t+1 for some t>=0.

The last equality comes from an even L input with k=c/2 and b+4=4*2^t, giving x=b-k+2,y=2k+5. The other even-to-odd branches enter x'=4 or 6. This complete necessary parent law is Lean Inverse.odd_large_parent. It deliberately overapproximates the regular parents by ignoring reachability and guards in subsequent sieves.

For X_j, both coordinates >=7. An odd X_j has neither regular parent. The feeder equation 3X_j=8*2^t+1 would imply 3*2^(2j+2)-2^(t+3)=3j+4. If t+3<=2j+3 the left side is at least 2^(2j+2)>3j+4; otherwise it is negative. Hence all even j are impossible and Inverse.root_halt_odd_index is the sharpened authentic-root equivalence.

## 4. Uniform feeder exclusion through prescribed inverse depth

Write X=X_j. After any integral inverse regular word of length d, the coordinates are

    x=(A X+B)/2^d, y=(C X+D)/2^d,

with A,C positive odd integers, A+C=2^(d+1), B,D<=0 and B+D>=-d*2^d. Initial (A,C,B,D)=(1,1,0,0). H updates to (A,A+2C,B,B+2D-2^(d+1)); L updates to (2A+C,C,2B+D,D). The bounds follow immediately by induction and are kernel-checked in Coeff.coeff_good/coeff_exact.

At depth d<=j-2, the minimum coordinate is at least X/2^d>=7: at every inverse step one coordinate halves and the other increases (H subtracts one after adding half of a coordinate >=2). Thus only the three large-parent alternatives matter. If an even feeder occurred there, multiplying its equation by 2^d gives

    (2A+C)*2^(2j+2)-2^(d+t+3)
      = (2A+C)(j+1)-2B-D+2^d.

The right side is positive and at most 2^d(4j+2d+5)<=2^d(6j+1)<2^(2j+2), since j>=d+2. The left side, if positive, is at least 2^(2j+2): if its second exponent is >=2j+2 it is a positive multiple of that power; otherwise 2A+C>=3 gives the bound directly. Contradiction. Consequently for every j>=n+2, a reached X_j admits at least one regular inverse word of length n. This is a paper derivation from the coefficient and parent theorems.

## 5. Binary extinction via synchronized inverse-word amplification

For a ray (a t+b,c t+d) with a,c positive odd, each regular inverse H or L is compatible with exactly one parameter bit r modulo 2. After restriction t=2t'+r, the new slopes are (a,a+2c) or (2a+c,c), again positive odd. The child_correct/child_wrong lemmas in Ray.lean check this affine identity. Thus each word of length n is compatible on exactly one residue class modulo 2^n. Count histories with multiplicity. For the population N at a binary prefix, N(prefix0)+N(prefix1)=2N(prefix); zero is absorbing and initial N=1.

A collision creates arbitrarily many synchronized histories, following the general amplification principle used by Agent21 for Machine C. Write m=x+y. The two inverse words HL and LH both end at mass m-1. If m=2 mod 4, each is integral precisely when x=2 mod 4; their final x difference is (m-2)/4, their y difference its negative. The identity is Ray.collision. In particular, for any L>=0, if m=2 mod 2^(L+2), their outputs are congruent coordinatewise modulo 2^L. Such outputs have identical compatible word sets for the next L bits: each inverse step divides one difference by two and adds it to the other, and congruence modulo 2 ensures matching compatibility. This follows by induction.

From any good ray steer to a uniform collision mass by following L+2 H inverses, each on its unique compatible digit. The mass slope is now a multiple of M=2^(L+2). At most M-1 further H inverses decrease the constant mass one at a time until m=2 mod M, uniformly over the unread parameter. The x slope is still odd, so precisely one two-bit prefix makes x=2 mod4 and realizes both words HL,LH.

Define F(0)=0 and F(k+1)=2F(k)+4+2^(F(k)+2). This upper bound includes steering, two collision bits and the recursively chosen amplification suffix. Inductively some extension of length <=F(k) from any good ray realizes at least 2^k compatible histories: use L=F(k) to synchronize two branches, apply the induction to one, and transfer the entire resulting word population to the other by congruence. The two initial words distinguish histories even if configurations coincide.

For a threshold B>1 stop counting at the first prefix where N=0 or N>=B. The finite-tree mean identity implies the stopped expectation is 1, so the fraction of prefixes that ever reach B is <=1/B. Choose k with 2^k>=B, H=F(k). From every nonempty population below B, choose one ray and amplify it: among length-H extensions at least 2^-H hit B. Therefore the fraction of prefixes at depth n with nonempty population is at most

    1/B+(1-2^-H)^floor(n/H).

Let n tend to infinity and then B tend to infinity. The surviving binary residue fraction tends to zero. This proof is deterministic counting on finite trees; it does not assume independent branches, random machine trajectories, or numerical observations.

## 6. Density-zero stopping-index theorem

Begin with ray (t,t). At any fixed precision n, a candidate with j>=n+2 satisfies X_j=-j-1 mod 2^n. Section 4 forces an integral word of length n for every actually reached candidate; by Section 5 only a fraction tending to zero of these residues is possible. The map j -> -j-1 is a bijection of residues. For any epsilon choose n with surviving fraction <epsilon. All j>=n+2 that reach the terminal diagonal belong to those residues, hence the upper natural density of reached candidate indices is zero. This proves the stated arbitrary-precision restriction on the full infinite stopping family. It does not exclude every exceptional j.

## 7. Evidence and research direction

[Reproduction dossier](../im-results/agent3-688-diagonal/README.md). Local Lean 4.36.0-rc2 compiles all six modules with only standard axioms in the named declarations. The explicit feeder inequality and full finite-tree extinction/counting arguments in sections 4-6 are paper-level proofs. The full source import is pending. A billion collapsed steps from the authentic root did not halt, but that is only finite evidence. Next: exploit the negative shadow (X,Y)=(-x,-y), whose inverse maps halve a coordinate, and show extinction at depth <=j-2 (or stronger quantitative threshold) for every remaining j, or otherwise construct a real terminal witness. The theorem does not establish BB(6).
