# Double-window rank barriers for the q0 signed path

**Strongest result.** The source-interface theorem `q0_chain` proves exclusion of the entire parameter interval

    1,000,000 <= u <= floor((41*16^K-22-6*K)/24)

provided the finite certificates `barrierFast a k=true` hold for every a in {4,7,13,23,41}, 5<=k<=K. `chain_cover` is an unconditional arithmetic theorem covering every scale, with no gaps; `q0_chain_all` isolates the remaining infinite mathematical problem: prove those five barrier families for all k>=5. No #429 decision or BB(6) upper bound follows yet.

For K=30 the 130 Boolean certificates all evaluate true. The exact gap-free range is 1,000,000 through **2,270,764,492,799,231,282,877,337,061,312,255,308** inclusive. The original lower interval below one million is the separate prior Q0MacroFinite certificate. The new numeric result is **native-computed, not kernel-only**: Q0BarrierNative.lean explicitly uses native_decide and its printed axiom profile includes native_chain_5_30._native.native_decide.ax_1_1. The generic proofs do not use that axiom. An independent exact Python integer implementation checks the same 130 pairs using carry-state endpoint prefilter and terminal cone (barrier_chain.py). This is a finite computational strengthening of the q0 reduction, not an all-scale proof or an original full-machine decision.

## Mathematical mechanism

The signed path from Q0MacroCore has rank p'=p+l, l in {3,4,5,6}, and y'=(y+dp+c)/16, with strict interior 0<3y<p. At a rank B=a*16^k, the first crossing has rank B+b, 0<=b<6. If

    24*u+22+6*k <= B
    B+5+12*k <= 48*u+37,

then a necessary q0 path has at least k past steps and 2k following steps. For the past word w, Q0RankBarrier gives the crossing ordinate a*Dn(w)+e with 3e<=a+b. The next k digits v are a small Carry trace reading w; the next k digits z are a Carry trace reading v. The first row starts at (b,e), ends at (q1,e1); the second row begins at precisely (q1,e1). The two rows are searched simultaneously, sharing the middle digit in each column, and the strict initial cone is tested exactly. The bound b+3k<=q1<=b+6k and carry bound permit finite seam enumeration. No ordinate of size 16^k is enumerated.

For speed, compute the complete one-row endpoint overapproximation by deduplicated forward propagation from (b,e), and only search actual seam candidates in it. `rowLayers_complete` proves inclusion of every real carry endpoint. `barrierFast_sound` proves absence of all strict-interior crossings when the fast checker returns true. `path_barrier_of_noCross2` lifts any crossing absence theorem to a rank interval; `q0_fast_barrier` plugs in the fast checker. The coefficient chain 4,7,13,23,41,64 (the last is 4 at the next scale) has adjacent ratios <2; the arithmetic proof verifies margins and all overlaps, including the initial 23 and 41 at k=5. All theorems above use the existing Source interface and q0 equations n=23+32*u, x+24*u+19=13*2^n, y+13=2*x.

## Polynomial-width alternative

Q0ConeCarry.lean gives an exact history-free strict-cone test. Let T=L(w), B(w)=bD(w)+E(w), and t=b*r+c_r-r*l where l is remaining cost. Then B(r::w)=t+16B(w). Start c1=0, c2=T-b, l=T; at each column replace c1 by floor((c1+t)/16), c2 by floor((c2-3t)/16), l by l-cost(r). At the end require l=0, c1<e, c2<a-3e. Both inequalities are strict and the Euclidean signed floor equivalence is proved in Lean. Since l, c1, c2 are O(k+b) for fixed b (geometric contraction), and the two carry rows have O(k+a+b) ranks/ordinates, a deduplicated frontier has polynomially many possible states in k at fixed a,b. Q0BarrierDP.lean implements this alternative with hash-set layer deduplication and proves every actual crossing is retained. It is not a practical speed improvement: the initial DP benchmark was much slower than seam-prefilter DFS, because it enumerates the total past cost T and all seam candidates. Retain the compression for future symbolic/parametric proofs; use Q0FastBarrier for finite checking.

## Reproduction

Local Lean 4.36.0-rc2 compiled actual original Q0MacroCore and Q0RankBarrier blobs 06821faeb7c97a2b6f65adb68cdc2f707dcfa03e / 9272b3dfdff8895d0fe2d677cc35bf2b2be29ead, then exact new modules Q0DoubleBarrier, Q0FastBarrier, Q0BarrierChain, Q0ConeCarry and Q0BarrierDP, with only propext, Classical.choice, Quot.sound on exported generic theorems. Q0BarrierNative compiled with the explicit native axiom above. In a directory with these files, set LEAN_PATH=. and run lean -o Module.olean Module.lean in dependency order. Direct `by decide` proved barrierFast 13 8=true and barrierFast 13 20=true axiom-free; the latter took about 7 seconds. Aggregate kernel-only reduction of all coefficients was too slow with the initial evaluator. A separate `by cbv` test proved barrierFast 41 5=true using propext. Do not conflate these individual kernel samples with kernel certification of the full chain.

Remaining: an all-scale mathematical proof (or a stronger alternative certificate sequence), not a larger arbitrary finite sweep. A coefficient may fail at particular scales: e.g. a=3 had genuine strict 2-row crossings in exploratory scans at k=5,14,18,24, so a universal claim about all coefficients is false. Finite chains of much larger scale do not resolve the unbounded family.
