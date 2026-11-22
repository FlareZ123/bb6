# Agent 24: token-normalizer continuation through the residual-2 branch

**Status:** source-lemma derivation and exact integer arithmetic; not yet Lean-compiled. This continues the unresolved token input at the end of RootRemainderOneTail.md.

## Parameterized token state

Define:

~~~text
S(x,r) = tok_DR([2,x,1,1,1,1,0], [], 0^r ++ [1])
~~~

The pinned source lemmas yield three useful transitions.

### Subtract-three cycle

For x >= 3:

~~~text
S(x,r)  -->+  S(x-3,r+4)
~~~

Raw cost: 6r+35.

- r applications of tok_DR_zero (4 each);
- tok_DR_1_nil_28 (28);
- r+1 applications of tok_EL_1 (2 each);
- tok_EL_add3 (5).

For N successive cycles starting at S(x,3), the total is:

~~~text
sum(j=0..N-1) (6*(3+4j)+35) = 12*N^2 + 41*N
~~~

### Zero-remainder branch

At x=0:

~~~text
S(0,r)  -->+  S(2r+7,3)
~~~

Raw cost: 8r+77.

After r tok_DR_zero steps, tok_DR_1_nil_28, and r+1 tok_EL_1 steps, the state is:

~~~text
tok_EL([0,1,1,1,1,0], [], 0^(r+4) ++ [1])
~~~

Then:

- tok_EL_0_cons gives tok_CR([2,1,1,1,0], [], 0^(r+4) ++ [1]);
- r+4 tok_CR_zero steps give tok_CR([2r+10,1,1,1,0], [], [1]);
- tok_CR_1_nil_33 and tok_EL_add3 give S(2r+7,3).

Cost:

~~~text
4r + 28 + 2(r+1) + 1 + 2(r+4) + 33 + 5 = 8r+77
~~~

### Residual-2 branch

At x=2:

~~~text
S(2,r)  -->+  CR(0^5 ++ [1] ++ 0^(r+3) ++ [1], [0])
~~~

Raw cost: 6r+46.

After the same initial r-zero reduction and tok_DR_1_nil_28, r+1 tok_EL_1 steps leave:

~~~text
tok_EL([2,1,1,1,1,0], [], 0^(r+4) ++ [1])
~~~

Apply tok_EL_2, four tok_EL_1 steps, and tok_EL_exit_zero. The left list becomes 0^5 ++ [1] ++ 0^(r+3) ++ [1]; the empty right suffix bumps to [0].

For completeness, the analogous x=1 branch gives CR(0^(r+9) ++ [1], [0]) at cost 6r+41.

## Specialization to the unresolved root token input

The final section of RootRemainderOneTail.md gives, with n=8,841,438:

~~~text
tok_DR([2,0], [], 0^3 ++ [1] ++ 0^(4n+6) ++ [1])
~~~

The initial source-lemma sequence is:

- three tok_DR_zero steps;
- tok_DR_succ;
- 4n+7 tok_CR_zero steps;
- tok_CR_1_nil_33;
- tok_EL_add3.

It reaches S(8n+12,3) at raw cost 8n+67 = 70,731,571. The preceding DL-right-one entry contributes another 4 raw steps.

Exact parameters:

| Stage | x | subtract-three cycles N | resulting r |
|---|---:|---:|---:|
| Initial | 70,731,516 | — | 3 |
| First zero branch | 0 | 23,577,172 | 94,308,691 |
| Second zero branch | 188,617,389 | 62,872,463 | 251,489,855 |
| Residual-2 branch | 2 | 167,659,905 | 670,639,623 |

The arithmetic is:

~~~text
x1 = 2*(3+4*N0)+7 = 188,617,389
x2 = 2*(3+4*N1)+7 = 502,979,717 = 2 (mod 3)
~~~

Thus the third batch takes (x2-2)/3 cycles and enters the residual-2 branch.

| Component | Raw steps |
|---|---:|
| Initial token prefix to S(x0,3) | 70,731,571 |
| First subtract-three batch | 6,670,597,440,875,060 |
| First zero branch | 754,469,605 |
| Second subtract-three batch | 47,435,361,822,007,411 |
| Second zero branch | 2,011,918,917 |
| Third subtract-three batch | 337,318,131,809,364,405 |
| Residual-2 branch | 4,023,837,784 |
| **From token input to residual-2 CR state** | **391,424,097,933,204,753** |
| Including preceding DL-right-one entry | **391,424,097,933,204,757** |

The resulting stack state is:

~~~text
CR(0^5 ++ [1] ++ 0^670639626 ++ [1], [0])
~~~

Its CR left head is 0, so this endpoint is not in the source's CR halting branch.

## Suffix-preserving general tail

The source helper chain in root_countdown_general_tail generalizes to a suffix T:

~~~text
EL([0], [0,x] ++ T)  -->+  D_0(x-6; T)
~~~

for x>6, with raw cost 47 (12 outer source transitions). In the current draft, the h7 call is missing one zero: it must receive remainder [0,0,x-3] ++ T, so that its output matches the existing h8 two-zero sweep. This is a proof-script correction; the target and raw cost remain unchanged.

From the residual-2 CR state, the ordinary source clauses give:

~~~text
CR(0^5 1 0^(r+3) 1, [0])
  -->+ CR(1 0^(r+3) 1, [10])
  -->+ CR(0^(r+3) 1, [0,13])
  -->+ CR([1], [2r+6,13])
  -->+ EL([0], [0,2r+9,13])
~~~

The first four transitions cost 2r+27 raw steps. Applying the suffix-preserving general tail with x=2r+9 and T=[13] costs another 47, reaching:

~~~text
D_0(2r+3; [13]) = D_0(1,341,279,249; [13])
~~~

The combined cost from the residual-2 CR state is 2r+74 = 1,341,279,320.

## Further suffix-preserving countdown

The source-derived recurrence from RootRemainderOneTail.md is:

~~~text
D_n(c;T)  -->+  D_(n+1)(c-3;T)
~~~

with raw cost 24n+69, preserving T. Since:

~~~text
1,341,279,249 = 3 * 447,093,083
~~~

the suffix-preserving countdown reaches:

~~~text
D_447093083(0; [13])
~~~

at additional raw cost:

~~~text
12*N^2 + 57*N = 2,398,706,723,881,644,399
~~~

The endpoint still has CR left head 0, so it is not in the CR halting branch. The zero-reset with suffix [13] is the next unresolved transition.

## Conditional cumulative raw-step arithmetic

The preceding RootRemainderOneTail.md gives a conditional cumulative total of 153,499,683,790,849 raw steps through D_0(26,524,315;[0,0,2]). The suffix-preserving countdown to D_8,841,438(1;[0,0,2]) costs 938,052,814,856,094.

Combining that conditional prefix with the present source-lemma derivation and the further suffix-preserving countdown gives:

~~~text
2,791,222,375,654,775,419 raw steps from blank
~~~

to D_447093083(0;[13]).

This is **not a certified runtime lower bound**: the prior root path, suffix-preserving maps, generalized tail, and token composition still require kernel-checked Lean proofs. It is a reproducible source-lemma target for the next formalization step.
