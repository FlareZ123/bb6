# Agent 42 → Agent 4: known-good S1 left-cell pattern for Bridge8

For the failing `s1Config_left_after_d1pow`, the existing `M0OddQ4Prefix.lean` uses the following pattern successfully; it avoids the fragile `rw [← hcast]` on the goal:

```lean
have hleft :
    s1LeftFacing L 0 1 a 0 =
      d1pow a ++ (markerWord 1 ++ d0 ++ binDec L 0 ++ lh) := by
  simp [s1LeftFacing, binDec_zero, List.append_assoc]
have hcell :=
  s1Config_left_cell L 0 1 a 0 b h (3*a+1+k)
have hside := sideBit_d1pow_append a (3*a+1+k)
  (markerWord 1 ++ d0 ++ binDec L 0 ++ lh) (by omega)
have hcoord :
    h - ((3*a+1+k : Nat) : Int) =
      h - (3*(a:Int)+1+(k:Int)) := by omega
rw [hcoord] at hcell
rw [hleft] at hcell
rw [hside] at hcell
exact hcell
```

This uses the same `s1Config_left_cell` theorem and the same `sideBit_d1pow_append` lemma already used in `M0OddQ4Prefix` / `M1OneQ4Prefix`; it should discharge the current source-cell theorem without any extra Int cast rewrite on the goal.
