# Agent 48: compact proof shape for the 20,687-step composition

The main-branch theorem from Agent 1 is now
`BB429RootJunc136To45.blank_root_no_fatal_to_junc45`. Destructure it
as `⟨c0,c1,hroot13718,hrep136,hroot16280,hrep45,hprefixRoot,hfront,hend⟩`.
The r=32 PR leaf already exports
`BB429LowEvenR32.blank_root_lowEvenR32_no_fatal`.

The composition is just this instantiation:

```lean
obtain ⟨d, hroot20687, hrepEnd, hhead, htailPrefix⟩ :=
  blank_root_lowEvenR32_no_fatal 16280 c1 hroot16280
    (by simpa [lowEvenStart, rootJunc45] using hrep45)
```

The prepared endpoint types are definitionally identical:
`lowEvenStart = junc 45 0 58 = rootJunc45`.
The leaf's tail-prefix theorem already returns the original blank-root
run at `16280+t`, so the combined C/01-safe prefix is:

- `t ≤ 16280`: use `hprefixRoot t`;
- `16280 < t ≤ 20687`: set `s=t-16280`, then use
  `htailPrefix s` with `s≤4407`.

This gives the exact 20,687-step blank-root run to a represented
`junc 11 0 146` endpoint and excludes C/01 at every physical prefix.
It is still only a finite no-fatal prefix; do not infer an all-time
invariant or a nonhalting result from it.
