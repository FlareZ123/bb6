# Three new polynomially growing Raw34 cylinders proved nonhalting

**Status:** unconditional all-completion mathematical theorems source-accepted by Lean 4.36.0-rc2. These are three distinct five-hole machine cylinders, each with a completely explicit unbounded tape-growth recurrence. They are new accepted local results rather than a complete Raw34 parent Cover or a BB(6) determination.

## The two 4n+3 triple-sweep machines

Two seven-instruction refinements of the canonical eight-hole Raw34 parent have the following exact transition tables:

```
P_A = 1RB1LD_1RC---_0RD0RA_1LC1RD_------_------
P_E = 1RB---_1RC---_0RD0RE_1LC1RD_---1LD_------
```

In `P_A`, the blank-tape computation enters state A on a marked symbol via C1=0RA, and A1=1LD returns to D. In `P_E`, the same intermediate turning action is performed by E using C1=0RE and E1=1LD. The exact source [Raw34TripleSweepGrowth.lean](../im-results/agent50-raw34-firsthole/Raw34TripleSweepGrowth.lean) defines the two partial machines separately and proves their common recurrence parametrically by a Boolean `useE` flag.

Let `rep [true] n` mean a block of (n) marked tape cells and define the ordinary zipper configuration

```lean
family n := ⟨3, [false] ++ rep [true] n ++ [false,true,true], []⟩
```

In this family, the machine is in state D at a fresh zero immediately to the right of an expanding solid block of ones, separated from the two leftmost ones by a zero. From the exact blank start, the machine reaches `family 0` after three transitions. At the (n)-th frontier, a three-move C1→A/E1→D0 sweep moves left across each of the (n) marked cells; a one-move D1 sweep traverses them back to the right. The exact kernel-checked step law is

```lean
growth (useE : Bool) (n : Nat) :
  run0 (p useE) (4*n+3) (family n) = some (family (n+1))
```

Thus the exact time of the (n)-th frontier is (3+sum_{k<n}(4k+3)=3+2n^2+n). All epoch lengths are positive. The source-proved `never_of_growth` therefore yields `BB6.Agent50Raw34TripleSweep.never` for **all compatible total six-state machines**, without assuming anything about their five remaining instructions.

**Accepted original-source evidence:** [run 46087571719](https://github.com/FlareZ123/bb6/actions/runs/46087571719), artifact [15240036445](https://github.com/FlareZ123/bb6/actions/runs/46087571719/artifacts/15240036445), zip SHA256 `ffc82bd60a89382a0aee44d1e82d4edaa6dca9ad6839e2fb7cb52a1965f7b04`. The reusable 3-step left and 1-step right identities, the all-time induction, and both specializations `A_never`, `E_never` compiled in Lean 4.36.0-rc2 with exactly `[propext, Quot.sound]` as axioms.

## One 4n+4 alternating-block machine

A third seven-instruction Raw34 refinement is

```
P_alt = 1RB---_1RC---_0RD0LD_1LC0RE_1RD---_------
```

Its tape grows an alternating marked/unmarked pattern. The source [Raw34AlternatingGrowth.lean](../im-results/agent50-raw34-firsthole/Raw34AlternatingGrowth.lean) defines the exact family

```lean
family n := ⟨3, [false] ++ rep [true,false] n ++ [false,true,true], []⟩
```

At each fresh right frontier, the C1=0LD/D0=1LC two-step leftward macro transforms a marked/unmarked pair into its complement position on the other side of the head. The D1=0RE/E0=1RD two-step rightward macro transports the alternating pattern back. A fixed four-step turnaround adds another `10` tape block. The exact original-source theorem states

```lean
growth (n : Nat) :
  run0 p (4*n+4) (family n) = some (family (n+1))
```

The blank-tape entry requires three steps, giving exact frontier times (3+2n(n+1)). Again, the source's `never_of_growth` establishes `BB6.Agent50Raw34Alternating.never` for every total completion, no simulation-time cutoff and no dependence on unspecified table instructions.

**Accepted original-source evidence:** [run 46087707935](https://github.com/FlareZ123/bb6/actions/runs/46087707935), artifact [15240244203](https://github.com/FlareZ123/bb6/actions/runs/46087707935/artifacts/15240244203), zip SHA256 `b23bf78983ed542d2b1f4b6b36650c618e31d57cc1ad315d4c8802c12099922f`. Both two-step sweep lemmas, the exact family recurrence and universal `never` theorem compile with only `[propext, Quot.sound]`.

## Exact additional coverage

Each of the three sources specifies seven distinct state/symbol entries and leaves five entries unrestricted; each resulting cylinder contains precisely `25⁵=9,765,625` complete physical six-state transition tables (including possible halts in never-queried entries). They are pairwise distinct by their literal C1 and D1 instructions and none belongs to the 1,206 previously certified depth-three side-cycle cylinders or the older 85+closed-component families. All three were among the long-running rather than recurrence-closed depth-three frontier branches.

The updated exact [25-ary physical-cylinder union audit](../im-results/agent50-raw34-firsthole/count_accepted_union.mjs) includes the three new fully source-accepted `P_A,P_E,P_alt` partial tables. It passed [CI run 46087926979](https://github.com/FlareZ123/bb6/actions/runs/46087926979), artifact [15240564330](https://github.com/FlareZ123/bb6/actions/runs/46087926979/artifacts/15240564330), SHA256 `0615ab9a7d9e702e37c68d7939d0ab2ec8648df3d605b3e72b394b00ae877338`. It certifies an additional **`3×25⁵=29,296,875`** distinct total tables beyond the earlier union of 97,509,765,625, for a revised local Raw34 total of **97,539,062,500** complete tables proved nonhalting. The remaining **55,048,828,125** physical tables extending Raw34 are outside these certificates and must not be mistaken for halting machines.

This source-accepted three-family result is a reusable illustration that time-consuming growth need not require expensive trace expansion: one may prove an exact finite macro-step of length two or three, then compose previously source-proved arbitrary-length sweep lemmas to derive an all-time polynomially growing family. The remaining hard branch with E1 unknown is not affected by this proof.
