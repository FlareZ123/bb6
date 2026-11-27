# All binary triple-containing G words halt

**New all-parameter source-clause theorem (paper proof); [Lean source append](GeneralTripleBarrier.append.lean) is prepared, full source acceptance pending.** It supersedes the restricted tail language in
[DoubleSuffixBarrier.md](DoubleSuffixBarrier.md). This is not an authentic
blank-root verdict.

## Statement

For M>=1, let G(M,U)=CR([0],0^M U), where U is a finite word over the
pair first coordinates 0 and 1. If U contains 111 as a substring, then
G(M,U) reaches a configuration with no next defined transition. The
following exact-cost algorithm computes its raw time, and the elementary
bound is

    T <= 2M + 3n^2 + 27n - 11,  n=|U|>=3.

The cost convention is the number of defined primitive transitions
ending at the configuration where the next step is undefined, as in
the pinned source ReachesPlus/step.isNone interface. It is not a claim
about the convention-dependent extra halting instruction in BB scores.

Source pin: google-deepmind/cryptids@3647718b5df22e1a61462dec0376bd204526285a,
BusyBeaver/BB6/Accelerations/M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC1RA.lean,
blob 7e1ac8acb4454a43d0354ea9a41be0cbda40a88c. All rewrites below use
the named source clauses at lines 303–380. There is no inferred affine
period or probabilistic assumption.

## 1. A token grammar invariant

Use the exact common token encoding of ordinary pairs:
(a,b) on the right encodes token a+1; the left uses just first
coordinates. See DoubleSuffixBarrier.md for the source definitions
and the high-token double identity. Work with tok_CR(X ++ [0,0], W, L),
where W is arbitrary. The two final tokens ensure the first encountered
zero can use tok_EL_0_cons. For W empty they are physical blank padding.

Call X **good** if it is nonempty, its first token is positive and not
2, and its tail is a concatenation of single tokens other than 2 and
the two-token block [1,2]. Equivalently, every 2 in X has a preceding
1, and that predecessor is not the first token of X.

For a good X, CR can consume left 0 at cost 2, increasing the first
token k to k+2. Or it can consume left 10 at cost 5, replacing k by
[1,k+3]. Both preserve goodness: k is positive and not 2, the
remaining paired tail is unchanged, and all new non-one head tokens
are at least 3.

If the first non-one token of X is high, write X=1^d [a+3] T, d>=0,
a>=0. The tail T is paired (the consumed high token cannot be the
first member of a [1,2] block). The new exact identity from the
separated-double theorem, now for arbitrary d, is

    tok_CR(1^d [a+3] T [0,0],W,11[c]L)
       -> tok_CR(1^(d+4) [a] T [0,0],W,[c+1]L),

with cost 41+6d. It follows from tok_CR_1_1_cons_25,
d tok_EL_1 steps, tok_EL_add3, d+2 tok_DR_zero steps and
tok_DR_succ. The new X is good even if a=2: at least four preceding
ones are available, the first one is not used to pair it, and T
retains its paired decomposition. If c=1 this exposes 2 and halts
in another two steps. If c=0, the left prefix 110 has become 1,
strictly decreasing its length by two.

## 2. The low-token branch is always fatal

Suppose X is good but its first non-one token is 0 or 2 (or absent).
For any left 11[c]L, tok_CR_1_1_cons_25 first produces

    tok_EL(X [0,0],W,00[c+2]L).

Let B be the longest prefix of X over tokens 1 and 2; let b1,b2 count
its ones and twos, and z count trailing ones. If X is exhausted,
the next token is the first sentinel 0.

Every 2 in B has its preceding 1 inside B. Consequently B decomposes
into single 1 and [1,2] blocks, and P=reverse(B-1) belongs to (0|10)*.
Using tok_EL_1 (cost 2) and tok_EL_2 (cost 7) scans all B to the
left, leaving 0 P 0 [c+2] L and the first token outside B pending.

* **Pending token 0.** There is a following token (including the second
  sentinel if X was exhausted). tok_EL_0_cons costs 1 and returns to
  CR with a nonempty token stack. The left prefix 0 P 0 is collectable
  in (0|10)*. Consume it using tok_CR_zero and tok_CR_1_0; these
  preserve nonempty K even if its head is low. The head c+2 is now
  fatal by tok_CR_add2_halts. Total cost including the original
  double is **32+4 b1+10 b2**.
* **Pending token >=3.** Since we are in the low branch, B contains at
  least one 2 (otherwise X had a high first non-one token). Thus
  P=0^z 1 Q, where Q begins with 0 and is collectable. tok_EL_add3
  initiates DR (5); DR transfers z+1 leading zeros (4(z+1)); then
  tok_DR_succ removes one from the encountered 1 (3), returning
  to CR with left 0 Q 0 [c+2] L. Its binary prefix is collectable,
  so the same two CR rules expose the fatal high head. Total
  **40+4 b1+10 b2+2 z**.

The count in the first case is
25+(2b1+7b2)+1+(2b1+3b2+4)+2.
For the second it is
25+(2b1+7b2)+5+4(z+1)+3+(2b1-2z+3b2+1)+2.
No hypothesis about values in W or the untouched left tail L is
needed. The low branch is genuinely fatal; it is not a claim that
all arbitrary unpaired token words are fatal.

## 3. Termination of the binary triple reduction

Suppose the left begins with a binary word containing 111, followed
by any tail. While the current binary word still contains a triple:

1. Consume a leading 0 or 10, preserving goodness and the triple.
2. Otherwise the word begins 11 and has a third digit c. If the
   token stack takes the low branch, Section 2 proves halting.
3. In the high branch apply the double identity. If c=1, halt.
   If c=0, replace 110 by 1 and preserve goodness; the pre-existing
   triple lies entirely beyond that 110 and remains present.

Each continuing step removes one or two digits. Thus induction on
binary word length proves halting for every such word and every
good X, even with arbitrary untouched tails. In particular there
is no need to assume a minimum separation between double-one blocks.
This replaces (0|01|0011)* by unrestricted binary suffixes.

## 4. Authentic G encoding and exact cost

Encode G(M,U) as tok_CR(1^M (U+1) [0,0], [], [0]).
The source's ordinary pair and token definitions agree because
second coordinates vanish modulo 1. The initial corridor costs
23+2M (tok_CR_zero, tok_CR_add2_nil_21, M times tok_EL_1).
Scan U at 2 per zero and 7 per one. Then tok_EL_0_cons and
tok_CR_zero cost 3, leaving the left reverse(U) followed by
0^(M+1)1 and right K=[3]. Pad K with [0,0] on the blank tail
without changing the physical tape. X=[3] is good, and reversal
preserves the existence of 111. Section 3 applies.

The time is exactly 2M+26+2#0(U)+7#1(U) plus the costs of the
deterministic CR algorithm in Sections 1–3. The executable
implementation is [general_triple_barrier.js](general_triple_barrier.js).

For the stated bound let r be the number of binary digits removed
before a continuing step. Always r<=n-3. The current |X|<=1+2r:
0 does not enlarge X, 10 adds one token, 110 adds four and
removes two binary digits. A continuing high double costs at
most 41+12r. Charge 21+6j to the j-th removed digit (zero-indexed):
one digit pays for a zero; two consecutive charges sum to 48+12r,
enough for a 10 or a high double. Hence continuing cost is at most
sum_{j=0}^{n-4}(21+6j)=3n^2-27. The terminal high costs at most
43+12(n-3)=12n+7. Either low case costs at most
40+10|X|<=20n-10 (since z<=b1). For n>=3 the latter also bounds
the terminal high. The entry costs at most 2M+26+7n. Summing gives
T<=2M+3n^2+27n-11.

## 5. Computational evidence and proof boundary

Executed the arithmetic algorithm against the original-source-clause
transcription, with no affine extrapolation, for every binary word
of length 3–15 containing 111: 42,287 words, all exact halting times
agreed. The paths included 50,945 high double rewrites, 4,690
terminal zero-token branches and 291 terminal high-after-two
branches. Maximum observed leading-one run d=13, post-entry
halting cost 345. An additional 36 cases sampled arbitrary good
token stacks and untouched nonbinary tails, including all three
terminal mechanisms; all matched.

A useful boundary counterexample to an overbroad proof: with
unpaired X=[2,2], a prepared CR triple can lose its high marker
after 101 source-transcribed moves and reenter a growth corridor.
The Good condition is essential to this argument. This is not a
nonhalting verdict for that prepared configuration.

The finite tests are not the proof. The source-clause induction
above is the mathematical advance; the direct [Lean formalization](GeneralTripleBarrier.append.lean) using the pinned source clauses is now prepared. It extends the kernel-accepted separated-double source closure without importing the older hazard append files. Full kernel acceptance remains the next gate. No
authentic #85/#490 blank trajectory has been shown to enter the
expanded region. No parent Cover or numerical BB(6) bound follows.
