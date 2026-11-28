# Raw11 q0-148: exact even-gap carry normal forms and the three-turn source bridge

**Status, 2026-11-28:** The exact arbitrary-length even-gap transducer theorem in `Q0148EvenCarryOutput.lean` is **kernel accepted** in [pinned Lean 4.36 source-closure CI run 46114949710](https://github.com/FlareZ123/bb6/actions/runs/46114949710), with all six printed `_output` proofs free of `sorryAx`. The deeper original-source return and all-marker induction remain **proof candidates awaiting kernel audit**, accompanied by finite original-table regressions. These are intermediate results, **not** a source Cover, a proof of full q0-148 nonhalting, or a BB(6) solution.

## Original source and the missing bridge

One-hole table `1RB1LC_1RC0RE_0LA0LD_1LA0RF_1RB1RD_0RC---`; the missing entry is F1. Agent5's exact open-table macros are in `../agent5-weighted-tnf-queue/Q0148BoundarySweep.lean`: `carryFold`, `twoBlankTurns`, `anotherBlankCycle`, `ARightToEOne`, and `markedHopN`. The proposed boundary arithmetic invariant/return is in `../agent5-weighted-tnf-queue/q0-148-boundary-recurrence.md`. The challenge is to prove that *the actual raw source machine* has the proposed positive return, not merely to prove that the gap-vector map preserves an abstract language.

Define chunk alphabet `A=alternating` (bits `10`), `M=separatedMarker` (bits `11010`), and carries `S=eleven`, `T=elevenZeroOne`, `U=one`. For a finite natural-number list `ns=[n₁,...,n_k]` let
```
 E(ns) = A^(2n₁) M ... A^(2n_k) M
 N(ns) = M A^(2n₁) ... M A^(2n_k).
```
These definitions work for arbitrary k and all n_i≥0; no simulation cutoff or cardinality assumption is involved. The precise all-length transducer laws are
```
 carryFold U (A^r M) = (A^(r+2),S)
 carryFold S (A^(2r) M) = (M A^(2r),S)
 carryFold S E(ns) = (N(ns),S).
```
In particular, `N(ns) M = M E(ns)` as literal chunk lists. This identity means `carryFold` **preserves all even gap lengths while moving the markers** rather than just returning the same carry.

## The harder a=3 branch resolves in exactly two additional cycles

For the qE right-blank boundary chunk stream `C=E(ns) A A`, write `s=scanCost(C)`. Successive exact carry outputs are:
```
 stage 0, twoBlankTurns:
   carryFold S C                = (N(ns) M, U)
   next input chunks            = M N(ns) M

 stage 1, anotherBlankCycle with tok=A:
   carryFold S (M N(ns) M A)    = (M M N(ns), T)

 stage 2, anotherBlankCycle with tok=M:
   carryFold S (M M N(ns) M)    = (M M M N(ns), S).
```
Each equality follows by finite-state word induction, marker rotation and the existing exact source transducer. Symbolic source times simplify to
```
  twoBlankTurns:           5s + 26
  U-to-T blank cycle:     4s + 38
  T-to-S blank cycle:     4s + 50
  total:                 13s +114.
```
The original physical word length is `B=s+4`, so the combined source time is `13B+62`. The **output state is qA0 with leading right tape `1010 ++ outputBits(M M M N(ns))`**, and qA's left tape is blank up to the arbitrary untouched suffix. Three leading `M` markers versus one in the a=1 branch account algebraically for the **two additional markers** in Agent5's proposed a=3 gap recurrence, with the interior gaps untouched at this stage.

The second Lean root `Q0148ThreeCarryCycles.lean` expresses this as `three_blank_turns_source` by composing `twoBlankTurns` and `anotherBlankCycle` twice with **seven blank left padding bits and three extra blank right padding bits**. These explicit paddings prevent silently assuming an extra blank when joining finite-source computations. The theorem's conclusion is a strict **defined original-table run** for every finite `ns` and arbitrary untouched external tails `L,R`. Lean acceptance remains to be established.

The simpler a=1 case has `C=E(ns)`, normalized carry `S`, qA0 after `5s+26` original steps, and leading right tape `1010 ++ outputBits(M N(ns))`. For either case, when `ns=prefix++[n]`, the right tape begins `(10)^(2n+2) 110`, so the existing `ARightToEOne (2n)` source lemma can enter the leftmost E1 marker in another `4n+6` steps. Formalizing the full right-return and the following `markedHopN` sequence remains the decisive unsolved piece.

## Reproduction and proof status

- `Q0148EvenCarryOutput.lean`: accepted all-length original-transducer even-gap normal forms, generic word append, and terminal carry laws. Independent pinned source-closure workflow 46114949710: **success**, printed axioms contain no `sorryAx`.
- `Q0148ThreeCarryCycles.lean`: marker rotation, second/third carry formulas and exact-source three-cycle composition. These files import the existing source macro module rather than rebuilding or replacing source semantics.
- Direct independent JS interpretation of the literal original partial table checked **150 parametrically chosen finite `ns` lists** of up to seven blocks, with different arbitrary left/right nonblank tails, at exactly `13s+114` source steps. All 150 yielded the predicted qA0 head and complete named output tape prefix/tail; this is an internal finite regression, **not** proof of universal validity. The Lean files contain the mathematical generalization and are the authoritative proof target.

**Next action:** source-compile the two new files against pinned Lean 4.36.0-rc2, repair any failing goals, then use the exact right-output factorization to join the original `ARightToEOne` and `markedHopN` macros into the universal positive boundary return. Do not mistake a successful source subroutine for the full raw one-hole Cover.

## Arbitrary marked-hop train: the missing all-marker induction is now explicit

After the blank-turn and first E1 source gadgets, the remaining difficulty is an arbitrary number of original-table marked E1 hops. The source-level word algebra has a sharp uniform formulation. For every `r>=0`, the same finite-state carry satisfies

```
  carryFold U (M A^(r+2)) = (A A M A^r, U)
  carryFold U (M A)       = (A A, T)
  carryFold U (M)         = (A A, S).
```

For any finite list `rs`, put `G(rs)=concat_{r in rs}(M A^(r+2))` and `O(rs)=concat_{r in rs}(A A M A^r)`. **There is no assumption on marker count, gap parity or gap size beyond these displayed natural parameters.** The exact transducer identity is `carryFold U G(rs)=(O(rs),U)`. The crucial telescoping identities for every `rs,z` are

```
  O(rs ++ [z]) A   = A A G(rs) M A^(z+1)
  O(rs) A A        = A A G(rs).
```

These are what make the boundary gap arithmetic exact: the first marker-crossing output keeps old crossed gaps unchanged, decrements only the far-left gap, and creates one new group. Specifically, for arbitrary `n,j,rs,z>=0`, `L,R`, the literal original F1-open table has the positive source step

```
  qE, left = 10 inputBits(A^(j+2) G(rs ++ [z])) 000 L,
      right= 010 A^n 110 R

  -- after (4 + 4 scanCost(leftChunks)) + (13 + 2n) TM steps -->

  qE, left = 10 inputBits(A^(n+2) M A^(j+2) G(rs) M A^(z+1)) 0 L,
      right= 0 R.
```

This is `ordinary_hop_source` in `Q0148SourceHopSection.lean`. It remains true when `z=0`, yielding a short `M A` far-left suffix. A final exceptional hop with this short suffix has the **exact original-source output**

```
  qE, left = 10 inputBits(A^(j+2) G(rs) M A) 000 L,
      right= 010 A^n 110 R

  -- same positive TM time formula -->

  qE, left = 10 inputBits(A^(n+2) M A^(j+2) G(rs) M) 0 L,
      right= 0 R.
```

The low endpoint is therefore far-left gap **one** rather than an undefined transition; it is `final_two_hop_source` in `Q0148ExceptionalSourceHop.lean`. The high endpoint has far-left gap **three**.

`Q0148MarkerTrain.lean` folds the ordinary step inductively over **any finite list of future right-side markers**, preserving explicit external zeros and an exact total source time. If the far-left countdown `z` is at least the list length, it reaches the last marker with the high endpoint. `Q0148LowMarkerTrain.lean` handles the case with countdown exactly two fewer: it runs the ordinary prefix, the penultimate `z=0` hop, and the final `M A -> M` exception. This gives the **all-marker source mechanism for both head-height possibilities** of Agent5's boundary invariant, assuming these Lean candidate files compile.

Writing `n0,n1,...,n_H` for the successive right-marker parameters, the terminal gap vectors implied by these exact stack identities are

```
   high: [3, n0+3, n1+3, ..., n_(H-1)+3, n_H+4]
   low:  [1, n0+3, n1+3, ..., n_(H-1)+3, n_H+4].
```

For the original stable boundary `g=(a,g1,...,g_(m-1),4)`, the parameters after the first blank return are the **old** `g2-1,g3-1,...,g_(m-1)-1,2` followed by **one** zero if a=1 or **three** zeros if a=3. Thus the displayed high/low formula *literally simplifies* to Agent5's conjectured `F(g)`. The head-height constraint `g1 in {m+a-3,m+a-1}` is equivalent to the starting far-left countdown being either the number of remaining marked hops or two fewer. The abstract recurrence closure was already established by Agent5; the new work is the all-depth **original-source correspondence**.

**Validation boundary:** The full Lean chain remains a proof **candidate**, not an accepted `NeverHalts` theorem. Direct literal partial-machine execution checked 120 nonterminal and 140 terminal arbitrary-gap source configurations (both with nontrivial external tails), all matching their exact source durations and left/right outputs; finite regression is not universal proof. Source CI initially exposed and then repaired five errors in the shared imported `Q0148BoundarySweep.lean`; subsequent jobs are checking the new all-length lemmas. Most important remaining integration: prove the exact boundary-word/first-E1 parameter-list splice, then connect the high/low final stack to `F(g)` and to the 147-step blank base. The exceptional base is **not** a 293-step boundary epoch: from `(3,4)` its first next E1 is at 293, three marked hops add 57+85+113, and the first next **boundary** is `(3,3,3,4)` after **548** source steps.


## Exact physical boundary encoding — no assumed tape grammar

The all-length carry proofs above must apply to the **actual physical boundary tape**, not only to syntactically convenient source chunk words. The link is a simple algebraic bit identity, valid for every number of interior gaps, and is the correct bridge from the boundary invariant P to the input of the original-table sweep theorem.

Let the *physical* left-to-right tape word at right-boundary E1 be
```
 W(a;u₁,...,u_k) =
   (10)^a 110 (10)^(2u₁+1) 110 ... 110
   (10)^(2u_k+1) 110 (10)^4,
```
with E reading the third (zero-based index two) `1` of the final `(10)^4`. Here `a∈{1,3}` and each `u_i≥1` encodes an odd old interior gap `g_i=2u_i+1≥3`; k may be zero (the exceptional base). Let `physLeft` be the bits from the head *towards the left*, inclusive, so it is the reverse of the physical left-to-right prefix ending at the head. Set `v=[1,u_k,...,u₁]` (the *head-side* gap source exponents).

**Exact physical-to-source identity:**
```
  physLeft ++ 0
    = 10 ++ inputBits(evenBlocks(v) ++ A^(a−1)).
```
The right-side bits after E1 begin with `01` and are zero otherwise. Thus `Q0148BoundarySweep.twoBlankTurns` applies literally, with enough explicit untouched zero padding; its source chunks are not a heuristic recognition grammar. In particular, for base `(3,4)` one obtains the actual 147-step blank checkpoint `qE1,l=10965,r=2` (left-stack integer read low-bit-first), since `10 A² M A²` is exactly the nearest-first left stack plus one exterior zero.

The identity has a short elementary proof by reversing each fixed bit block. Put `A=10`, `B=110`, `M=11010`, and `Ā=01`, `B̄=011`. For every natural r,
```
  (01)^r 0           = 0 (10)^r,
  (01)^(r+1) 011     = 010 (10)^r 11.
```
The first identity is induction on r; the second follows immediately. For `a=1` or `3`, `(01)^a 0 = 010 (10)^(a−1)`. Reversing the physical left-of-head word produces the fixed initial prefix `1 (01)^2 011`, then in turn the blocks `(01)^(2u_k+1)011,...,(01)^(2u₁+1)011`, and finally `(01)^a`. Each reversed interior block is `010 (10)^(2u) 11`. Its final `11` followed by the next block's leading `010` gives precisely the source marker `M=11010`. The trailing reversed `(01)^a 0` closes the last marker and leaves exactly `(10)^(a−1)`; the initial fixed prefix plus its first `010` equals `10 (10)^2 M`. Concatenation gives the displayed source identity for **any k**.

I independently checked the complete original physical reversal against the chunk encoding on 500 deterministic example vectors, including k=0 and both a values; all matched, but the above two string equalities and list induction are the *actual all-length argument*. A dedicated Lean version can be added when the deeper source-return modules have passed their checks.
