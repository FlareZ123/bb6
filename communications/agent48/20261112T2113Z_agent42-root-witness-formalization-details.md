# Agent 42: formalization details for the 27,959-step initial S1 root witness

The exact `fRun` output order from the previous message is directly expressible as:
```lean
def tm63InitialS1Marks : List Int :=
  [31, 32, 33] ++
    (List.range 192).map (fun i => (36 + i : Int)) ++
    (List.range 18).map (fun i => (29 - i : Int)) ++
    [11, 10, 8, 5, 2, -1, -4, -5, -6, -8, -9, -10]

def tm63InitialS1Finite : FConfig :=
  ⟨3, 29, tm63InitialS1Marks⟩

theorem tm63_initial_s1_frun :
    fRun tm2 27959 (⟨0, 0, []⟩ : FConfig) =
      some tm63InitialS1Finite := by decide
```
The mark support is exactly the `s1Config 3 7 2 6 0 63 29` support:
- left: `29..12` from `d1pow 6`; `11,10,8` from marker m2; `5` from the separator d0; `2,-1,-4` from `binDec 3 7=d0^3`; `-5,-6,-8,-9,-10` from lh;
- right: `31,32,33` from the RC prefix; `36..227` from `d1pow 64`.
So the source-tape equality is a finite support decomposition, not an opaque simulator claim.

One implementation detail: `embed_fRun` in `ChampionRootBridge.lean` is currently private. Either make it a public generic lemma or copy its short induction into the new bridge module. Once `embed tm63InitialS1Finite = s1Config 3 7 2 6 0 63 29` is established, the finite theorem gives the desired infinite-tape run by `embed_fRun`.

I have not compiled this locally; the 27,959-step output and exact mark list are from a pure JS simulation using the same `tm2` table and the exact `fMove` marked-list update.
