# S4 exact 18-prefix return renormalization into 386 suffix gates

**Central mathematical contribution.** For the original source-defined S4 return map `P=G509;G290;G219`, a periodic 18-digit projected prefix induces a **source-semantics-preserving return map on every finite suffix**. For the authentic return-5457 prefix, the 20,971,520-return projected cycle beginning at relative time 1,310,720 reduces to precisely **386 ordinary source `G` gates with positive constant offsets**. There is no trailing head-add operator. This is a structural approach to the authentic suffix history and first stopping event. It does not yet prove S4 nonhalting or determine BB(6).

**Proof status:** The general algebra is formalized in [S4SuffixBoundary.lean](S4SuffixBoundary.lean), which proves `H_split`, `G_split`, `G_bump`, and `bump_bump` for **all finite suffixes**, including empty ones. [S4BoundaryWord.lean](S4BoundaryWord.lean) proves the fully quantified `wholeWord_split` theorem for any finite word of positive `G` offsets. Both modules compile locally in Lean 4.36.0-rc2 using **exact copies of the source `H/G` definitions** with only standard axioms `[propext, Quot.sound]`; the pinned original-source CI is still being checked. The nine-/18-prefix initial root uses the existing original-source-certified 5457 checkpoint and prefix causality. The 18-coordinate period, 386-gate extraction and exact offset list are finite **C++20 arithmetic certificates** [s4_suffix_macro.cpp](s4_suffix_macro.cpp), rather than Lean-kernel-reduced numeric equalities. The 21-million-step full-stack regression is a source-shaped finite model, starting at a later simulator-derived stack; its true-root bridge beyond 5457 is not independently Lean-certified. Do not promote this to an unconditional original-source root decision.

## General source-map factorization

Write `G_c` for the partial original S4 odd-drain on finite natural stacks, and `gp_c` for its source-proved total fixed-length prefix projection. Its original `H` recursion starts with active head `a=p[0]+c`, scanning the digits of a prefix `p` from left to right.

For any fixed nonempty prefix `p` and any finite suffix `S`, the action on the suffix is determined by the carry scan over `p` alone. Exactly one of three cases applies:

1. The scan meets an even active head before the final prefix digit. Then the stage succeeds and leaves `S` unchanged.
2. The scan reaches the final prefix digit with even active head `a=2d`. The stage succeeds and transforms the suffix by `A_d`, defined on a nonempty tail by `A_d(b::R)=(b+d)::R`, and on the empty tail by `A_d([])=[d-1]`. Here `d>=1` because the original active head is positive.
3. The scan crosses every prefix digit with odd active head, ending at `a=2d-1`. The stage acts on `S` by the **original partial** `G_d`, including its halting condition.

Consequently, in each case the source stage on `p++S` equals `gp_c(p) ++ (T_{p,c}(S))` when `T` succeeds, and the original stage returns `none` exactly when the boundary `G_d` returns `none`. These claims also cover the empty suffix because the source convention is `G_c([])=H(c-1,[])`.

The two elementary rewrite laws are
```text
A_d ∘ A_e = A_(d+e)
G_c ∘ A_d = G_(c+d)
```
for positive `d,e,c`, as equalities of partial maps on **all** finite tails, including `[]`. They follow directly from adding `d` to the first original tail digit, and from `A_d([])=[d-1]`. Identity actions disappear. Thus additions accumulated before the next `G` gate can always be absorbed into its offset, preserving the exact first stopping event. A trailing addition, when present, must be retained.

## Concrete periodic renormalization

Let `p18` be the first 18 digits of the source-certified reduced S4 state at return 5457. Put `B=327680`, `T=64B=20971520`, and
```text
p* = pp^(4B)(p18)
   = [283,906,982,3490,3734,5935,13580,109210,171050,
      366446,435438,366335,527037,2639156,3037351,3252483,
      6310511,24221543].
```
The [independent finite-prefix arithmetic certificate](deep_cycle_census.cpp) verifies `pp^T(p*)=p*` exactly.

Process the `3T=62914560` source-stage offsets from `p*`, always advancing the total 18-digit projection, and record each boundary action. The arithmetic gives:

| Boundary event or statistic | Exact value |
| --- | ---: |
| Head-add events `A_d` | 402 |
| Partial suffix gate events `G_d` | 386 |
| Remaining head-add after normalization | 0 |
| Normalized gate-word length | 386 |
| Sum of original G offsets | 10,435,793,071 |
| Sum of head-add offsets | 11,039,042,637 |
| Sum of normalized G offsets | 21,474,835,708 |
| Minimum / maximum normalized offset | 5,178,393 / 309,630,238 |

Denote the 386 positive normalized offsets in chronological order by `e_1,...,e_386`, defined algorithmically by [the extractor](s4_suffix_macro.cpp). Let `Q=G_(e_386) ∘ ... ∘ G_(e_1)` with `Option` short-circuiting. The generic factorization yields the **all-suffix return identity**
```text
P^T (p* ++ S) = Option.map (p* ++) (Q(S)).
```
This is an exact mathematical reduction for **every** finite tail `S`, conditional only on the finite verified prefix period and the source `H/G` semantics. If a component `G_(e_i)` returns `none`, its index identifies the first halting stage within the original `T`-return block. The extractor can also record the corresponding original phase/stage. No assumption of an infinite authentic root orbit is required for the identity.

The offset-sum identity is an independent mass check:
```text
sum_i(e_i+2) = 21474835708 + 2*386
             = 21474836480 = 1024*T.
```
Each successful original `P` return adds 1,024 units of stack mass, so the normalized `Q` word carries the entire per-block mass influx into the tail.

## Exact model regression on the authentic-root continuation

The source-certified first 5457 returns end with the 18-digit `p18`. A finite exact-integer simulation of another `4B` original `P` returns obtains a 24-digit stack with prefix `p*` and suffix
```text
[24423525,56750562,67602890,162126013,335820941,659578070].
```
The program runs the 386 normalized `G` offsets on this suffix. It separately simulates all 20,971,520 original `P` returns on the 24-digit stack, and asserts complete stack equality at the end. Both calculations succeed. The resulting 10-digit suffix is
```text
[22012582,64906604,241039393,1583055453,388528736,
 3150551875,2840572411,10520913460,1984778983,1984778980].
```
The partial `G` implementation is separate from the total prefix `gp` implementation, and the hand-derived factorization supplies the reason for equality for arbitrary suffixes. This single regression is evidence against implementation mistakes; it is not itself a proof of the universal statement.

## Research consequence and next decisive task

The difficult true-root history now has an **exact induced suffix map in the same family of odd-drain operators**. Every 20,971,520 source-reduced returns can be replaced by 386 much cheaper source gates once the root enters the projected `p*` section. This offers a large speedup for genuine-tail forward/inverse analysis and makes a potentially useful renormalization hierarchy explicit.

The next mathematical objective is an **all-time survivor invariant for `Q` starting at the authentic section suffix**, or a failing effective gate providing a genuine halting witness after bridging the finite section to the original source. A repeating finite prefix does not imply a repeating full stack, and the 386 effective gates leave infinitely many potential stopping events. A Lean source-interface proof of the generic factorization is the next formal-verification obligation; the numeric 18-period certificate should be kernel-checked if it becomes part of a decisive root theorem.
