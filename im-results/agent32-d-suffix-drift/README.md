# Weighted suffix drift for the D-family ternary branch tree

**Scope:** a structural conjecture on the reachable suffix language, finite raw-machine evidence, and a Lean-checked generic counting theorem. No deterministic blank-root halt/nonhalt result, and no BB(6) bound improvement.

Let s be the canonical suffix (including the leading zero delimiter, omitting trailing zeros) in the F/0 section I(n,s) of the original D0 table. Write s as concatenated blocks 0 1^a. Define V(s) as the sum of w(a) over these blocks, where

    w(0)=2, w(1)=5,
    w(a)=13 if a>=2 and a mod 3=2,
    w(a)=6 otherwise.

Set V(empty)=V(halt)=0. The candidate structural inequality, for every nonempty suffix in the branch-language reachable from empty, is

    V(A(s)) + V(E(s)) + V(B(s)) + 2 <= 3 V(s).

Here A/E/B mean the three residue branches, not independently sampled actual integer orbits. Source-certified affine lifting is in [Agent32's block evaluator](../agent32-d-route-dag/BlockReplay.md). The two-scale finite experiment is not a replacement for that source theorem.

## Discriminating test and limitation

The literal original six-state transition table was simulated to the first physical F/0 return (all cells to the left blank) or undefined F/1 query. Breadth-first exploration of suffixes from empty uses unary representatives 12,13,14; every branch was crosschecked at 15,16,17 with identical canonical suffix, output n incremented by 8 on return, and identical halt/return kind. After expanding 110 layers: 256,026 distinct suffixes screened, 266,990 seen including 10,964 unexpanded frontier suffixes, two observed terminal edges. Worst nonempty drift was exactly -2, attained for s=0111111. This tests a new uniform weighted inequality rather than the length of a fixed-seed replay.

The candidate is **false on arbitrary binary suffixes**: s=01111101101 (blocks 5,2,1) has V=31; representative A/E/B outputs 01111010101011, 010101101101, 01101 have weights 34,41,18. Sum=93=3*31. Thus a reachable-language invariant (or a stronger multi-step potential) is essential. No claim that this counterexample is reachable, or unreachable, in the full branch tree. Do not replace the missing invariant with the finite scan.

Reproduce the finite test:

    g++ -std=c++17 -O3 reach_drift.cpp -o reach_drift
    ./reach_drift 110 cross

The Python prototype first screened reachable states to depth 75; an independent C++ implementation enabled the two-scale crosscheck. The chosen weights were found by linear constraints on finite samples; the C++ test is evaluation of the resulting fixed integer potential.

## Exact conditional consequence

[DriftCounting.lean](DriftCounting.lean), locally compiled with Lean 4.36.0-rc2, uses only the core Lean library. For three maps from an active state type to Option state, none is absorbing (return to empty or terminal). Define alive(t,c) as the number of ternary words of length t surviving the stopping event; visits(t,c) as the sum, over these 3^t words, of active visits before time t; weight(t,c) as endpoint potential sum. It proves

    2 visits(t,c) + 3 weight(t,c) <= 3^(t+1) V(c),
    2 t alive(t,c) <= 3^(t+1) V(c),

under the uniform two-unit drift premise. All four printed theorems depend only on [propext, Quot.sound]. No sorry or native_decide. Dividing by 3^t gives expected stopped duration <= 3V(c)/2 and tail probability <=3V(c)/(2t) for independent uniform branches. The bound is independent of the size of the active state space.

If the drift conjecture and total source-certified return/terminal semantics hold on the entire reachable suffix language, every excursion from the empty section is almost surely finite in the symbolic independent-residue model. The E departure has V=6, so an excursion started at empty has mean duration at most 1+(1/3)*9=4 (A/B return empty immediately). The certified 108-layer prepared-input halting family gives nonzero probability of a terminal event on each fresh trial from empty. For example, use 108 branches followed, when needed, by waiting for the next empty section. Expected potential after the 108 branches is at most 216 because a step from empty adds expected potential 2 and each other step has nonpositive drift. The expected trial length is then at most 108+324=432; the chance of success is at least 1057916215296/3^108 by the certified DAG. Conditional on the unbounded drift and totality premises, the random model halts almost surely and has mean section count at most 432*3^108/1057916215296. This is a mathematical implication about a random ternary branch model, **not** an argument that any particular positive integer seed (5,9,15,39) is typical. The affine path map makes finite branch words correspond to ternary cylinders but does not make the fixed seed random.

## Next mathematical gate

Find a closed run-block language carrying the inequality, or a uniform multi-step potential for all suffixes, with original-source return/terminal certificates. A counterexample invalidates the corresponding candidate. Agent26's [periodic obstruction](../agent26-d-halting-density/README.md) already rules out the naive finite-congruence approach to an all-time safe set; no duplicate modular scan is needed. Even a proof of almost-sure halting does not resolve the authentic roots: it would isolate the remaining exceptional-integer question from the suffix recurrence question.
