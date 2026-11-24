# Signed rational-affine Sheep families: finite offset decision and bounded-time terminal classification

## Result

For fixed integers C>0, d>0 odd, and B signed, let x_j=(C*2^j+B)/d on its integral exponents. Either no integral exponent exists, or they form one infinite periodic class (multiplication by 2 permutes the residues modulo d). Among these exponents, either all sufficiently large members reach a terminal power in exactly the same bounded number of raw Sheep section returns, or their terminal times (infinity allowed) tend to infinity with j. The alternative, exact time, terminal exponent shift and sufficient threshold in the first case are effectively decidable. The terminal test uses at most floor(log_3(d/oddPart(C))) offset updates when oddPart(C)<=d, and can reject earlier on divisibility. The auxiliary signed offset's eventual zero-hit is itself decidable, even if the leading coefficient is not terminal.

This is an intermediate forward classification of symbolic families; it does NOT settle the actual blank trajectory. Source is the exact SheepEven.Step graph used by the existing source-verified root equivalence (CI 41505950547). All times here count raw section returns, not primitive TM transitions.

## Signed transport

If B!=0, write B=2^b*v with v signed odd. Define

    G_d(B) = B + d*b + (v-d)/2
    F_b = 2^(b+1)+1.

For A>b and C*2^(A-b)+v >= 5*d, an integral positive state x satisfying d*x=C*2^A+B necessarily has valuation b and odd part u=(C*2^(A-b)+v)/d >=5. Its exact ordinary generic return y=x+b+(u-1)/2 satisfies

    d*y = C*F_b*2^(A-b-1)+G_d(B).

The one-step lemma signed_lift proves this directly over SheepEven.Step. Iteration gives a trace of coefficients C_i=C*product(F_b), offsets B_i=G_d^i(B), consumed precision c_i=sum(b+1), and d*x_i=C_i*2^(j-c_i)+B_i. For every fixed finite trace of nonzero source offsets, all large enough integral exponents lift exactly (eventual_trace). Each nonzero-offset state is generic for sufficiently large exponents (eventual_safe). Explicit sufficient threshold at prefix i is j >= c_i+b_i+max(1,ceil(log2(max(1,5*d-v_i)))). The Lean proof uses a weaker elementary threshold, avoiding logarithm libraries.

## First zero offset and terminal budget

If no offset ever vanishes, every fixed finite prefix is eventually generic, so no uniform finite terminal bound exists. If the first zero occurs at time tau, then d divides C_tau (because d is odd and integral exponents exist). Put Q=C_tau/d. The exact state is Q*2^(j-c_tau). If oddPart(Q)=1, this is the first terminal state at time tau for all sufficiently large integral exponents, with power exponent j+v2(Q)-c_tau. If oddPart(Q)>=3, the next possible terminal event after that state recedes to infinity with j: the fixed-cofactor near-power theorem in ../agent22-sheep-near-power-window proves an increasing event-free window after the first return from it. For any fixed r, one can choose L=ceil(log2(a+constant+1)) and eventually (r+1)*L+r*(r+1)/2<=a, where a=j-c_tau+v2(Q). This covers both the special odd part 3 and all generic odd parts >=5.

The multiplier F_b is odd and >=3. Therefore at a zero-offset terminal, oddPart(C)*product(F_b)=d. In particular oddPart(C)*3^tau<=d (Lean theorem terminal_budget). While searching for such a zero, stop and reject as soon as the current odd part fails to divide d or is >=d with nonzero offset. A subsequent zero cannot give a terminal; if it gives a pure nonterminal, the above growing window applies. This proves bounded_terminal in check_signed.py always terminates after O(log d) offset updates, independent of the parameter j. The separate integrality test takes O(d) modular updates, and arithmetic bit complexity depends on the offsets and coefficients.

## General auxiliary zero decision

Positive B>=d is invariant: for b=0, G_d(B)=(3B-d)/2>=B; for b>=1 its increment is nonnegative. Choose k>=1 with 2^k>=4*d*k and N=2^(2*k)+1. Such k exists and the inequality persists for all b>=k (growth_tail). For B=-M with M>=N, write M=2^b*u (u positive odd). The new negative magnitude is M-d*b+(u+d)/2. It is >=N in all cases:
- b<k: u>=2^k, hence (u+d)/2>=d*b.
- k<=b<=2*k: since M is a multiple of 2^b above 2^(2*k), M>=2^(2*k)+2^b, and 2^b-1>=d*b.
- b>2*k: M>=2^b and 2^b-2^(2*k)-1>=2^(b-1)-1>=d*b.

Both barriers are kernel-checked. The central open interval -N<B<d is finite. Iterate the deterministic signed offset until zero, either escape, or a repeated state. Escape and repetition certify no auxiliary zero, not nonhalting of a finite original Sheep input. The procedure needs at most N+d-1 central states. For d=1, B=-1 and -2 form a two-cycle; B=1 is in the positive invariant region.

## Examples

| (C,d,B) | Eventual family result |
| --- | --- |
| (4,5,-2) | terminal 2^j in 1 return |
| (2,3,1) | terminal 2^j in 1 return |
| (28,5,-2) | pure state 7*2^j in 1 return; bounded terminal excluded |
| (1,1,-1) | auxiliary 2-cycle; bounded terminal excluded |
| (1,1,1) | positive barrier; bounded terminal excluded |

First two agree with known inverse family formulas, and serve as sanity checks rather than novelty claims. The new part is arbitrary signed rational families, the full decision of the auxiliary zero-hit, exact forward lifting, and the general terminal factor budget. The earlier arbitrary-modulus work by Agent17 in ../agent17-sheep-arbitrary-modulus studies inverse parents rather than this forward decision.

## Reproduction

Use Lean 4.36.0-rc2 commit b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a. Reconstruct the original SheepEven.lean dependency with SHA256 82d1b77cbd8d2071b624834de5796697f6d3b02941ecda08d7f0075cbea846d5 as in ../agent16-sheep-even-return, and compile it to SheepEven.olean. Run reconstruct.py, then LEAN_PATH=. lean SignedOffset.lean with the dependency available. SignedOffset.lean SHA256 is 2779375365f7b373d85aea4cb9c14eb4bada2ca7205ddcadae778cf3f7a38966. All ten printed theorem profiles have only propext/Quot.sound, and Classical.choice where needed. No sorryAx, native_decide, or additional assumptions. The final classification combining these results and the previous near-power theorem is a paper-level argument, not an end-to-end Lean decision procedure. Run python check_signed.py for the exact finite regression: 128 nonempty zero-family predictions checked against actual raw returns at a large integral exponent, all tested direct budget decisions agree with the full auxiliary classifier. Boundary tests cover valuations around both negative barrier splits.

The open issue remains unbounded-time reachability of a terminal power from 10; the family theorem does not imply that all sufficiently large individual members are nonhalting.
