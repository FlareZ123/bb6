# Raw40 / A1=0LA / C1=1LC / leaf66: all-time nonhalting by a nested run drain

**Mathematical proof, executable finite entry, not yet Lean accepted.** Literal table
`1RB0LA_1RC0RE_0RD1LC_1LD1LA_---0RF_1RA1RF`.
Every completion of E0 is nonhalting. This is a single local leaf, not a completed parent or global BB(6) decrement.

## Entry and notation

[check_leaf66.js](check_leaf66.js), runnable with Node, replays exactly 93860 assigned primitive moves from blank and checks state A scanning zero, head +10, nearest-first left word (01)^11, right word 1^63, implicit zeros beyond both words. This is X_11 below. The checker executed successfully in the JS runtime; no native Lean verification is asserted.

At A0 write L=1^k 0 L' (the zero may be implicit) and let R be the nearest-first right word, with infinitely many implicit zeros. Suffixes in the following formulas are literal and untouched except where leading runs merge. Each arrow uses finitely many positive assigned primitive transitions, terminating at A0.

## Elementary A0 macros

The machine is A0=1RB A1=0LA B0=1RC B1=0RE C0=0RD C1=1LC D0=1LD D1=1LA E0=hole E1=0RF F0=1RA F1=1RF.

* R=0 1^b S, b>=1: A0,B0,C1 (left sweep over the old head and the k ones), C0,D1 yield left L', right 1^(k+b+2) S. The first zero to the left of the old head is preserved.
* R=00 1^b S, b>=1: A0,B0,C0,D1 give left 11 L, right 1^b S.
* R=000 S: A0,B0,C0,D0,A1 (left sweep erasing the old head and the k ones) give left L', right 0^(k+1) 111 S. This includes all-zero R.
* R=1^b 0^g 1^c S, b>=2: A0,B1,E1 erase the first two right ones; F1 scans the remaining b-2 ones and F0 writes the first zero. If g>=2, A is now scanning zero, with left 1^(b-1)00 1 L and right 0^(g-2)1^c S. The all-zero suffix is included. If g=1, A1 erases the first bit of the next run and then the contiguous F-written run, stopping at the second erased one. Left becomes 0 1 L and right 0^b 1^(c-1) S. E0 can only be encountered in the one-leading-one case b=1, which our proof avoids.

## Normalized return system

Normalize to A0 with right beginning with at least two ones. State (k,b,U,V) encodes L=1^k followed by the stack U of pairs (z,x), each denoting 0^z 1^x, and R=1^b followed by stack V of pairs (g,c), denoting 0^g 1^c. All x positive; left gaps z are 1 or 2. Right gaps positive. The path proved below has right c>=2.

A left push(z,k') prepends (z,k+1) to U and changes k to k'. A left pop removes leading 1^k and a zero: for empty U it sets k=0; for head (1,x) it removes the head and sets k=x; for head (2,x) it replaces it with (1,x) and sets k=0. For every rule take head (g,c) off V, leaving S; empty V means g=infinity and c=0.

| Condition | Left operation | New b | New V |
|---|---|---|---|
| g=1,b=2 | push(1,2) | c-1 | S |
| g=1,b=3 | pop | k+c+5 | S |
| g=1,b>3 | pop | k+6 | (b-3,c-1)::S |
| g=2 | push(2,b-1) | c | S |
| g=3 | push(1,0) | b+c+1 | S |
| g=4 | push(2,b+1) | c | S |

For g>=5 (including infinity), define C=c+3 if g=5 and C=3 otherwise. Let S'=(g-5,c)::S if g is finite and greater than 5, and S'=S otherwise.

| Condition | Left operation | New b | New V |
|---|---|---|---|
| b=2 | push(1,2) | C | S' |
| b=3 | pop | k+6+C | S' |
| b>3 | pop | k+6 | (b-3,C)::S' |

Here k,b on the right sides are OLD values. To derive the last table, apply the fourth elementary macro (g>=2) and then the third (g-2>=3, or blank). This leaves left 0 1 L and right 0^b 1^C followed by S'. If b=2 apply the second macro; if b>=3 apply the third, then the first. For g=1 the fourth elementary macro gives left 0 1 L and right 0^b 1^(c-1) S directly, then the same b=2 or b>=3 continuation. The g=2,3,4 rules follow from the fourth macro followed by zero, one, or two leading zeros respectively, using the first two macros where necessary; for g=3 the first macro pops the leading b-1 ones from the new left word, leaving 0 1 L. The original exploration matched 2512 consecutive normalized configurations in the first 100000 primitive moves. No finite agreement is used to infer the induction.

## Standard drain lemma

Write e=(1,1), and e^j for a stack of j copies. Define inc(U) by empty -> [e], (1,x)::W -> (1,x+1)::W, (2,x)::W -> e::(1,x)::W. Let T_j=(5j+3,3).

T_0 consumes in one normalized step:
(k,b,U,T_0::S) -> (0,b+4,(1,k+1)::U,S).

T_1 with b=6 consumes in three steps:
(k,6,U,T_1::S) -> (0,k+14,e::inc(U),S).
Indeed the g=8 rule pops left and puts T_0,T_0 before S. Apply the T_0 rule twice.

For j>=2 and x>=1:
(1,6,e^(j-2) ++ [(1,x)] ++ U,T_j::S)
 -> (0,x+5j+9,e^j ++ inc(U),S)
in exactly 2^(j+1)-1 normalized steps, with all b>=2 and right-run counts positive along the path.

Proof by strong induction on j. Split T_j by g>=5, then consume T_0. After these two steps the state has k=0,b=11, and right T_(j-1)::S. For stage i=1,...,j-1, k=0,b=6+5i, right T_(j-i)::S. For i<j-1 the left stack is e^(i-1) ++ [(1,2)] ++ e^(j-i-2) ++ [(1,x)] ++ U. At the final stage i=j-1 it is e^(j-2) ++ [(1,x+1)] ++ U. The split pops left, makes b=6 and replaces the right token by T_i,T_(j-i-1). For i=1 use the T_1 identity (k=2 except in the final stage, where k=x+1); for i>=2 the popped k is 1 and the induction hypothesis applies with parameter 2 except in the final stage, where it is x+1. For nonfinal i this gives b=6+5(i+1), k=0 and the claimed next left stack, using inc on its remaining head. For final i it gives b=x+5j+5, k=0 and e^(j-1) ++ inc(U), followed by T_0::S. Consume T_0 once. For j=2 the final-stage formula follows immediately from inc on [(1,x)] ++ U. Total steps are 2 + sum_{i=1}^{j-1} 2^(i+1) + 1 = 2^(j+1)-1. The suffix S is never read or modified. All stages use only the displayed positive rules.

## General gap drain

For n>=1, 1<=r<=5, c>=2:
(1,6,e^(n-1),(5n+r,c)::S)
 -> (0,5n+6,e^n,(r,c)::S)
in 2^(n+1)-2 normalized steps.

Indeed while the residual gap is greater than 5, the split ignores c and subtracts 5 from that gap. The first split and T_0 consume take two steps, giving k=0,b=11. If n=1 the left stack is now e and the drain ends. Otherwise at stage i=1,...,n-1 the left stack is e^(i-1) ++ [(1,2)] ++ e^(n-i-1), with k=0,b=6+5i and residual gap 5(n-i)+r. The split inserts T_i before the decremented gap. The standard lemma consumes it (parameter 2, using the T_1 case for i=1). For i<n-1, inc on the remaining nonempty e stack yields the next-stage formula; at the last stage inc(empty)=e, so the final left stack is e^n. The total is 2 + sum_{i=1}^{n-1} 2^(i+1) = 2^(n+1)-2. The final gap (r,c) is not consumed.

## Root recurrence and nonhalting

Let X_n denote (0,5n+8,e^n,[]), i.e. A scanning zero, nearest-first left (01)^n, right 1^(5n+8), implicit zeros. For n>=1, the normalized evolution is:

1. Empty-right case (g=infinity): (1,6,e^(n-1),[(5n+5,3)]).
2. General drain r=5,c=3: (0,5n+6,e^n,[(5,3)]).
3. The g=5 case: (1,6,e^(n-1),[(5n+3,6)]).
4. General drain r=3,c=6: (0,5n+6,e^n,[(3,6)]).
5. The g=3 case: (0,5n+13,e^(n+1),[])=X_(n+1).

Thus X_n -> X_(n+1) in exactly 2^(n+2)-1 normalized returns, each a nonempty sequence of assigned primitive transitions. Every intermediate b>=2; all right tokens used have c=3 or 6. Translation invariance removes the need to track head offsets. Blank enters X_11 by the checked finite replay. Consequently there are arbitrarily long assigned-transition paths from blank, and no completion can ever reach E0. This is an unbounded proof, not a fixed simulation cutoff.

## Integration

The old 1LC discovery bank had two unresolved leaves, 66 and 201. The latter has separate translated-cycle evidence from Agent42. Leaf66 can now be marked mathematically nonhalting, with formal integration still required. A Lean proof should establish the four elementary zipper macros, the normalized return system and the two strong-induction lemmas, then replay the finite entry in manageable chunks. Do not treat the mathematical status as a checked certificate or decrement the global roster.
