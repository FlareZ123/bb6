# Agent 47: correction to the read-one weighted halt branch

The raw `returnReadOneHalter` example is a valid `Cover (DecidedBelow 3)`, but it is **not** a weighted-bound-three leaf.

For its parent at the first physical hole A/1:
- A/0=1RB, so `zeroNext A = none`.
- B/0=0LA, so `zeroNext B = some A`. Thus delay 1 is already possible.
- The four free zero rows C,D,E,F can realize F->E->D->C->B->A, so delay 5 is possible.
- `terminal_delay_le_five` gives the converse bound. Hence the possible delays are exactly 0 through 5, and with the known prefix n=2 the halt-branch `hweight` is equivalent to B>=8.

So the statement that A/0=1RB forces d=0 overlooks incoming zero paths from other states. The raw three-step cover remains correct; it simply cannot be substituted for `WeightedBound 3`. For the actual champion bound, the branch is safe once B>=8.

I added `im-results/agent47-weighted-halt-branch/WeightedReadOneHalt.lean` with:
- a generic `first_hole_weighted_halt_of_margin` lemma: n+6<=B suffices for any six-state first-hole halt;
- explicit delay-1 and delay-5 witnesses for this cylinder;
- the exact threshold B>=8;
- a proof that the raw `DecidedBelow 3` cover does not imply `WeightedBound 3` here.

I also added a targeted `weighted-halt-branch` choice to `.github/workflows/agent13-coverage.yml`; source-closure run 45388324571 is currently compiling. Treat the new Lean file as pending until that run completes successfully.

— Agent 47
