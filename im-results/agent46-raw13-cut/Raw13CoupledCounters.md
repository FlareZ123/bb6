# Coupled-counter nonhalting theorem for raw13 parent 1093

**Theorem (mathematical proof; full Lean assembly pending).** Both partial machines with codes

    7 14 11 5 2 19 22 0 13 13 10 24
    7 14 11 5 2 19 22 0 10 13 10 24

avoid their sole unassigned transition (F1) forever from blank. Here a code is 4*next + 2*write + right, and 24 means unassigned. Consequently every completion is nonhalting. The two machines are the E0=0RD and E0=1LC hard siblings of the source-targeted parent 1093. The exact stuttering equivalence is kernel-checked in Raw13Detour.lean; it suffices to prove the first table safe.

This proof has three components: exact frame rules (kernel-checked in Raw13Frames.lean), a finite accelerated entry certificate (check_coupled_entry.py), and the all-time guard argument below. The latter and the finite jump arithmetic have not yet been assembled into Lean. No empirical long run is used as a proof of infinite behavior.

## 1. Notation and exact rules

Words are nearest-cell first, including the scanned cell on the left. Blank tails are implicit. Let F(L,W) denote state A, left word L, right word P pair(W), where P=01011 and pair(b)=1b. Write enc(x) for binary x, little-endian, with each bit b encoded as b000. A fixed-width encoding is denoted enc_m(x). Trailing zeros on the left do not affect the actual tape. Juxtaposition means concatenation. A right word W has a definite finite length because its encoding has a 1 in every pair.

Define scan by:
- scan(empty)=(0,empty);
- scan(0W)=(0,W);
- scan(1) and scan(1b)=(3,empty);
- scan(1bcW)=(6+a,V) when scan(W)=(a,V).

Each arrow below is a finite, strictly positive sequence of assigned transitions. All k,n are nonnegative.

(M) F(1^(2k)(1000)^n 0L,W) -> F(1^a 0^(4n)1L,V), where (a,V)=scan(0^k 1 W).
In particular k>0 gives a=0, V=0^(k-1)1W.

(M11) For n>=1, F(1^(2k)(1000)^n 110L,W) -> F(1^a 1L,V), where (a,V)=scan(1^(2n-1)0^(k+2)1W).

(S) For n>=1, F(1^(2k)(1000)^n 1001L,W) -> F(1^a 11L,V), with the same scan input as M11.

(S0) F(1^(2k)1001L,W) -> F(11L,0^k1W).

For independent checking: A with left prefix 11 removes two bits and prepends 01 to the right in two steps. Prefix 1000 removes four and prepends 1111 in four steps. Prefix 1001 replaces it by 01 and prepends 01 in six steps. On left 0L and right 1^j01c pair(W), the machine reaches E with left c11 0^j1L and right pair(W) in j+3 steps. E with left c11X and right pair(W) realizes scan(W) by returning to F(1^a X,V). Its elementary cases are: empty 13 steps, initial 0 nine steps, singleton 1 eighteen steps, two-bit 1b either 14 or 18, triple 1bd ten or fourteen steps to E with left d11 1^6X and remaining pairs. These finite identities plus induction give the rules. The Lean file checks the actual table for all cases, with arbitrary suffixes. The numeric tape projection in Raw13TapeValue.lean justifies ignoring left blank padding.

## 2. Ordinary double increment and finite jumps

Write W as a sequence of complete triples followed by 0,1,or 2 spare bits. Let v(W)=sum W[3i+2]*2^i over complete triples, n=floor(len(W)/3). If v<2^n-1, there is a first complete triple with third bit 0. Write

    W = (a_i b_i 1)_{i<j} a_j b_j 0 R.

Then scan(1W)=(6(j+1),R); set I(W)=0^(3j+2)1R. This increments v by exactly one and sets the first two bits of every visited triple to zero.

For an aligned left counter enc_m(x)U, assume x+2<2^m (or allow arbitrary width if U empty). Apply M with k=0 to the trailing 1 bits of x. It increments x to x+1, and prepends 6(j+1) ones, leaving R on the right. Apply M again, with k=3(j+1)>0, to the trailing 1 bits of x+1. The result is exactly F(enc_m(x+2)U,I(W)). This proves the double increment for both parities of x. The first step also works at x=2^m-2; the second may deliberately carry into U in the boundary arguments below.

Iterating d double increments is valid whenever v+d<=2^n-1 and x+2d<2^m if a suffix U is present. Without a suffix choose width large enough. The left becomes enc(x+2d) with the original fixed suffix. For d>0 the greatest triple index accessed is bit_length(v xor (v+d))-1: monotone addition crosses the binary boundary for that index but no higher boundary. Every lower index is accessed; the first two bits of those triples are therefore zero, and their third bits are those of v+d. Higher triples and incomplete trailing bits remain unchanged. This establishes the exact accelerated jump used by the entry certificate, without executing billions of increments.

## 3. A protected-suffix budget

For any finite word U define

    cap_i(U) = sum_{j: i+3j<len(U)} (1-U[i+3j])*2^j, i=0,1,2
    C(U)=min_i cap_i(U).

If C(U)>0, an ordinary I increment on U is possible and does not touch any suffix V in W=UV. It decreases cap_2(U) by one, and only clears bits in planes 0 and 1. Thus C decreases by at most one. Prepending an arbitrary bit b sends the three capacities to (1-b+2 cap_2, cap_0, cap_1). In particular arbitrary finite prepending cannot decrease C. We count an invocation of I as spending one unit, and prepending as free. A budget of B guarantees any sequence of at most B such increments, interspersed with prepends, while protecting V.

## 4. Drain lemma

Set D_h(t,W)=F(1^(6h)100 enc(t),W). If t>0, write t=2^s(2u+1), s>=0. There is an assigned path to D_0(u,W') spending at most 2^s units if s>0, or zero if s=0, and otherwise only prepending to the right word. This holds with a protected suffix whenever the prefix budget suffices.

### Odd t (s=0)

The left after its 6h ones is 1001 000 enc(u). Apply S0 with k=3h, then M with k=1,n=0. It reaches D_0(u,1 0^(3h)1 W). This costs no budget.

### Even t, h=0

Split the left as enc_s(1) U0, where U0=0001 000 enc(u). Put U1=1001 000 enc(u). (These suffixes are physical bit strings.) 
1. Use 2^(s-1)-1 double increments to bring the low s-bit counter to 2^s-1. Apply M with k=0,n=s to carry into the initial 0 of U0, using one I increment (scan(1W) supplies 6a ones, a>=1). The intermediate left is 1^(6a) enc_s(0) U1. Apply M with k=3a,n=0 to obtain enc_s(1) U1 and the I-updated right. First phase spends 2^(s-1).
2. Again use 2^(s-1)-1 double increments. Now the low all-1 counter is followed by U1, so apply S with k=0,n=s. Write H=ceil((2s-1)/3) and delta=3H-(2s-1) in {0,1,2}. Its scan input is 1^(2s-1)00 1 W. If delta=0 or 1 it consumes H triples then stops at a zero; result left 1^(6H)11 000 enc(u), right 0^(1-delta)1W. Apply M with k=3H+1,n=0 to reach D_0(u,0^(3H)1 0^(1-delta)1W), only prepending. If delta=2 the scan consumes both zeros and continues on 1W. Use one I increment, with scan(1W)=(6a,R). The result left 1^(6(H+a))11 000 enc(u), right R. Applying M with k=3(H+a)+1,n=0 gives right 0^(3H+1) I(W). Hence step 2 spends at most 2^(s-1), and the total at most 2^s.

### Even t, h>0

First apply M with k=3h,n=1; it prepends 0^(3h-1)1 to W and turns enc_s(1) U0 into enc_s(2) U0 if s>=2, or enc_s(0) U1 if s=1. For s>=2 use 2^(s-1)-2 double increments to reach low counter 2^s-2. The first M of one more double increment gives low all-1 with 6a leading ones, a>=1. Its second M (k=3a,n=s) carries into U0 to obtain enc_s(0) U1, with I-updated W. Thus cost so far is 2^(s-1)-1 (also zero for s=1).
Now apply 2^(s-1)-1 double increments from zero to 2^s-2. One further first M gives all-1 with 6a leading ones and right R, where I(W)=0^(3a-1)1R. Instead of an ordinary second M use S with k=3a,n=s. Its scan input is 1^(2s-1)0^(3a+2)1R. Since a>=1, it stops at a zero after H triples (same H and delta above); the left is 1^(6H)11 000 enc(u), right 0^(3a+1-delta)1R. Apply M with k=3H+1,n=0. This gives D_0(u,0^(3H)1 0^(2-delta) I(W)), just a prepend to the I-updated word. Total cost <=2^s-1.

### Iteration bound and output

Apply the lemma repeatedly until t=0 (after at most bit_length(t) applications). The exponents s>0 across applications are precisely lengths of the nonempty runs of zeros in the binary word of t, which ends in a high 1. If z is the total number of zero bits, the total cost is <=2^z when z>0, or zero when z=0: sum 2^s <= product 2^s for positive integer s (combine terms by 2^a+2^b<=2^(a+b)). Every application sets h=0. If the three highest bits of t are 111, the last two applications are odd: any preceding zero run may be consumed with the third-highest 1 but cannot consume the remaining two. Both last applications have h=0 and prepend 11, so the output begins 1111. (Two highest 1 bits alone would not suffice: a zero run could be consumed together with the penultimate 1.) Finally D_0(0,W') is F(1,W') modulo blank padding.

## 5. Closed root family

Consider F(1,W) with W beginning 111, ending V=0^9 1, and len(W)>=13 so those two parts do not overlap. We prove a positive return to the same family.

Let len(W)=3n+r, 0<=r<=2, v=v(W). The first three bits imply v odd. Do 2^n-1-v double increments with unbounded left width. Now v=max and left counter x=1+2(2^n-1-v_original), odd.

At overflow, scan(1W) consumes all full triples. If r=2 it yields 6(n+1) leading ones and no right tail. The following M with k=3(n+1) finishes the double increment; the new right word is 0^(3(n+1)-1)1 with plane value 2^n. There are then 2^n-1 ordinary double increments to the next overflow. Put N=n+1 in this case. Otherwise put N=n.

The remaining overflow has r=0 or 1: scan(1W) yields 6N+3 leading ones, no tail. The first M increments the odd counter to an even one; in the next M, after 3N+1 pairs of ones, a lone 1 is followed by the four zero bits of the even counter's first digit. Thus n=1 in that M, and the output is

    F(0^4 1 enc(y), 0^(3N)1),   y=2^N-v_original.

This identity uses x+1=2y, and includes the r=2 extension above. The number y is odd. If original r=0 then the last complete plane bit was 1 and the preceding three were 0, giving
2^(n-1)+1 <= v_original <= 2^(n-1)+2^(n-4)-1. Hence y has width n-1 and its top three bits are 111. If r=1 or 2 the three highest complete plane bits are 0, giving 1<=v_original<=2^(n-3)-1. In these cases y has width N and top three bits 111. These bounds use n>=4, and n>=5 in r=0. In every case y has at least four bits and t=(y-1)/2 has three highest bits 111, width at most N-1, and at most N-4 zero bits.

The new right word is U V, U=0^(3(N-3)), so C(U)=2^(N-3)-1. Since y=2t+1 the left is 0^4 11 000 enc(t). Apply M with k=n=0: scan(1W) consumes one triple and stops at zero; left becomes 1^7 000 11 000 enc(t), right R=0^(3N-3)1. Apply M11 with k=3,n=1: its scan input is 1 0^5 1 R, yielding (6,0^2 1 R). The outcome is D_1(t,I(W)), with exactly one unit spent, leaving budget at least 2^(N-3)-2.

The drain lemma now suffices: for N>=5 its cost is at most 2^(N-4)<=2^(N-3)-2; for N=4 t=7 and cost zero. The drain preserves V and returns to F(1,W') with W' starting 111. Since the new prefix has at least three bits separate from V, len(W')>=13. Thus the family is closed under positive assigned paths, which yields an infinite run by induction.

## 6. Reachable entry

Run python check_coupled_entry.py (standard library only). It starts at the exact blank configuration, takes 21 primitive steps to F(1,empty), and applies only the proved frame and bounded jump rules, or finite primitive replay when no frame rule matches. The first guarded entry occurs after 111 accelerated transitions, 23 of them jumps with total 8589945599 double increments. The trace SHA256 is d40e9be75650d0a46cf82c5b36808cb84fcbff75f9126bc0a07218406ccba917. The right word is length 170, begins with 26 ones, and ends in at least nine zeros followed by 1. The exact word is printed. This finite computation checks reachability rather than inferring nonhalting from a long trace.

Together sections 1–6 prove the base machine never queries F1, and the exact detour equivalence transfers the conclusion to the other sibling. A local certificate can be integrated through Raw13BinaryGraft.lean; the two leaves account for 50 represented literal completions, and do not close the other residuals of parent 1093. The overall BB(6) maximality question remains open.
