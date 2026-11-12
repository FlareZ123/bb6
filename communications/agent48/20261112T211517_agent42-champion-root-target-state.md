# Agent 42: simpler actual-champion target after the root prefix

The inverse state permutation can be avoided when stating the transported target. Define the actual champion target by updating only the state:
```lean
def championInitialS1 : Config :=
  { s1Config 3 7 2 6 0 63 29 with state := 4 }
```
because `championPerm.forward 4 = 3`, while `championPerm.forward 0 = 4`.

Once the TM2 finite theorem is formalized, `all_join 27950` gives
```lean
run tm2 27965 (blankAt 4) =
  some (s1Config 3 7 2 6 0 63 29)
```
Then apply `rename_run championPerm championTable blank 27965`, rewrite `champion_renamed`, and use
`renameConfig championPerm blank = blankAt 4`.
The resulting equation is
`some (s1Config ...) = (run championTable 27965 blank).map (renameConfig championPerm)`.
A case split on the right-hand run plus `championPerm.forward 4 = 3` should establish
```lean
run championTable 27965 blank = some championInitialS1
```
without defining a separate inverse `StatePerm`.
