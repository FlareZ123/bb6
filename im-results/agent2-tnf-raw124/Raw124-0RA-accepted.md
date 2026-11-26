# Raw124 F1=0RA: accepted local source-level audit

For `1RB---_1RC---_0RD---_1LD1RE_---1LF_---0RA`, all 24 children and the final weighted root have passed Lean 4.36.0-rc2 (b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a). The theorem `BB6.Agent2Raw124B0RA.bound_all : ∀ m, compatible pBranch m → WeightedBound 283 m` covers all 25^5 = 9,765,625 raw completions, including early halts and the weighted blank-delay correction. No claim is made about other F1 children or the full canonical roster.

## Reproduction

Use the existing `generate_bundle.py` and `complete-bundle-0RA.json.zlib.b64`, or reconstruct from workflow run [45582556219](https://github.com/FlareZ123/bb6/actions/runs/45582556219), source head aa141fa64772baf0df278ebe092cb4cb3c9ba9f7. Common artifact 15007681429 and child artifacts 15008745324, 15008246615, 15007952542, 15007731639, 15007163078 supply the source dependencies and 20 accepted child modules. In the historical K05 source only, replace the recursive-node identifier `p124` with `pNode124` (the collision with the parent abbreviation was already fixed in the current generator). In that shard directory the following commands completed successfully:

```sh
export LEAN_PATH="$PWD"
for k in 04 05 06 07; do
  lean -o "Raw124B0RAKidK$k.olean" "Raw124B0RAKidK$k.lean"
done
lean -o Raw124B0RAData.olean Raw124B0RAData.lean
```

Both `checkRoot` and `bound_all` report exactly `[propext, Classical.choice, Quot.sound]`; no sorry or native-decide axiom. The assembly uses the original `certified` source theorem and `WeightedTNFCertificate.sound`, not an alternative simulator. Source SHA256 of final Data module: `be7c26b3cd15e0044251ee13e71c82d0e58cc596f3860423a077d26ded430c55`. Its locally generated olean SHA256: `6ee93891b94b49eb827c0fc55a6dfc47c7562870b9d2804c5976d3d7b61794c7`. This is a completed local assembly with prior CI-built dependencies; a new all-in-one CI run is not asserted.
