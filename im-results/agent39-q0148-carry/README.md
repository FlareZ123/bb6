# Raw11 q0-148: source-accepted F1-open child-cylinder Cover via exact boundary carries

**Status, 2026-11-28 — F1-open child-cylinder Cover accepted:** `BB6.Agent5Q0148NeverCover.never_cover : Cover NeverHalts p` passed the exact transitive Lean 4.36.0-rc2 source-closure and axiom audit in [CI run 46178357131](https://github.com/FlareZ123/bb6/actions/runs/46178357131), pinned at source commit `4051a6e314624eb7276766ceb40daba45b643c84` (artifact `15276228192`). The audited theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`; the workflow rejects `sorryAx` and every nonstandard axiom. Thus **every total completion** of the F1-open table `1RB1LC_1RC0RE_0LA0LD_1LA0RF_1RB1RD_0RC---` is nonhalting from the blank tape. This closes only the one-hole F1-open child cylinder beneath the seven-hole Raw11 q0-148 parent; it does not close that entire seven-hole parent or BB(6). The earlier all-length even-gap and three-turn source sublemmas remain independently accepted in runs 46114949710 and 46115863435. The exact global parent membership/consumption edge is still open; do not decrement the Raw11 or Canonical38 residual count before its source-accepted join.

## Original source and the F1-open child cylinder

One-hole table `1RB1LC_1RC0RE_0LA0LD_1LA0RF_1RB1RD_0RC---`; the missing entry is F1. Agent5's exact open-table macros are in `../agent5-weighted-tnf-queue/Q0148BoundarySweep.lean`: `carryFold`, `twoBlankTurns`, `anotherBlankCycle`, `ARightToEOne`, and `markedHopN`. The boundary arithmetic invariant/return is in `../agent5-weighted-tnf-queue/q0-148-boundary-recurrence.md`. The formerly missing bridge from this invariant to the *actual raw source machine* is now closed by the source-accepted `never_cover` theorem below; the derivations here explain the exact all-length mechanism rather than a finite scan.

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

The second Lean root `Q0148ThreeCarryCycles.lean` expresses this as `three_blank_turns_source` by composing `twoBlankTurns` and `anotherBlankCycle` twice with **seven blank left padding bits and three extra blank right padding bits**. These explicit paddings prevent silently assuming an extra blank when joining finite-source computations. The theorem's conclusion is a strict **defined original-table run** for every finite `ns` and arbitrary untouched external tails `L,R`. **Kernel ACCEPTED: pinned Lean source-closure workflow [46115863435](https://github.com/FlareZ123/bb6/actions/runs/46115863435) completed successfully, including axiom audit of `three_blank_turns_source`.** This is an actual all-length original-source theorem, not merely a proposed formula.

The simpler a=1 case has `C=E(ns)`, normalized carry `S`, qA0 after `5s+26` original steps, and leading right tape `1010 ++ outputBits(M N(ns))`. For either case, when `ns=prefix++[n]`, the right tape begins `(10)^(2n+2) 110`, so the existing `ARightToEOne (2n)` source lemma enters the leftmost E1 marker in another `4n+6` steps. This right-return is now composed with the all-marker `markedHopN` sequence, the reset-to-train macros, and the packed epoch theorem in the accepted `never_cover` proof.

## Reproduction and proof status

- `Q0148EvenCarryOutput.lean`: accepted all-length original-transducer even-gap normal forms, generic word append, and terminal carry laws. Pinned source-closure run 46114949710: **success**, with no `sorryAx` in the printed output theorem profiles.
- `Q0148ThreeCarryCycles.lean`: accepted all-length a=3 three-boundary-turn original-source theorem `three_blank_turns_source`, including explicit blank padding and untouched external tails. Pinned run 46115863435: **success**.
- `Q0148MarkedHopCarry.lean`, `Q0148SourceHopSection.lean`, `Q0148MarkerTrain.lean`, and `Q0148LowMarkerTrain.lean`: their exact transitive source closure now compiles as part of the complete `Q0148NeverCover.lean` audit in run 46178357131.
- `Q0148NeverCover.lean`: accepted theorem `BB6.Agent5Q0148NeverCover.never_cover : Cover NeverHalts p`, all total completions of the literal F1-open table. Run 46178357131 audited the complete dependency closure and allowed only standard Lean axioms.
- `Q0148ThreeCarryCycles.lean`: marker rotation, second/third carry formulas and exact-source three-cycle composition. These files import the existing source macro module rather than rebuilding or replacing source semantics.
- Direct independent JS interpretation of the literal original partial table checked **150 parametrically chosen finite `ns` lists** of up to seven blocks, with different arbitrary left/right nonblank tails, at exactly `13s+114` source steps. All 150 yielded the predicted qA0 head and complete named output tape prefix/tail; this is an internal finite regression, **not** proof of universal validity. The Lean files now contain the kernel-accepted all-marker source generalization used by the full `never_cover` theorem.

**Next action:** retain this theorem as the exact `Q0148WeightedCover` source cut already registered in `generate-coarse-parent-shards.cjs` for the literal one-hole table. It closes that child cylinder only. Complete the other q0-148 branches and the actual seven-hole parent Cover; the 9.08 MB `Agent5Q0Coarse148Sub_root_18_r_1` blocker is a module-granularity problem, so regenerate/split it with a materially smaller `module_nodes` limit (about 2000) rather than replaying the unchanged module. Only after the parent Cover and exact 148→147 consumer pass may Raw11 residual counts change.

## Arbitrary marked-hop train: the all-marker induction is source accepted

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

**Validation boundary — child-cylinder theorem accepted; seven-hole parent remains open.** The full transitive closure of `Q0148NeverCover.lean` compiled and passed the axiom audit in run 46178357131. Its `never_cover` theorem is an unbounded original-source `Cover NeverHalts p`, not a bounded simulation: it composes the exact blank-start base, both reset branches, the all-marker high/low train, and the packed boundary epoch. Its scope is the one-hole F1-open cylinder `1RB1LC_1RC0RE_0LA0LD_1LA0RF1RB1RD0RC---`, which the q0-148 generator already registers as a `Q0148WeightedCover` region cut. It is **not** a Cover of the whole seven-hole q0-148 parent; the other branches and final parent source join remain open. No Raw11 or Canonical38 residual count changes yet.

The supplementary bit-level physical reversal theorem in `Q0148BoundaryGeometry.lean` is being audited separately (run 46178644824 was queued at the time of this revision). It is not a premise of the accepted `never_cover` closure: the accepted proof already uses Agent5's exact packed boundary algebra and blank-start encoding. The earlier finite regressions of 120 nonterminal and 140 terminal arbitrary-gap configurations remain corroboration only, not the proof.


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

I independently checked the complete original physical reversal against the chunk encoding on 500 deterministic example vectors, including k=0 and both a values; all matched, but the above two string equalities and list induction are the *actual all-length argument*. A separate Lean formalization of this physical-to-source bit identity is now in `Q0148BoundaryGeometry.lean`; its source audit is run 46178644824. This is a supplementary explicit tape-geometry lemma, not a premise of the already accepted `never_cover` theorem.
