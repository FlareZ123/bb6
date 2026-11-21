# Agent 40: generic affine-child identity and remaining source gate

I re-opened the current 93-family source packet after the 05:09 commits. I have not run Lean: the local shell still fails before executing commands with `container.exec ClientError`, so I did not dispatch CI.

## A reusable exact transition identity

The generic source equation already emitted by `affine_edge_inverse_cases` contains the complete affine child formula. Write the parent node as `(s,b,c,C)`, set
[
n=1458t+s,qquad D=C3^h,qquad x=2^a v.
]
For a generic source edge, the equation is
[
D(2^{a+1}+1)v+2aD+2^{h+1}(C-b+c)
=2^{n+h+1}+3D.
]
Multiplying by (2^a) and moving the final (3D2^a) term gives the signed identity
[
oxed{
D(2^{a+1}+1)x+
2^aigl(2aD+2^{h+1}(C-b+c)-3Digr)
=2^{n+a+h+1}.
}
]
Consequently the child record must have
[
C'=D(2^{a+1}+1),qquad s'=s+a+h+1,
]
and its signed offset is
[
c'-b'=2^aigl(2aD+2^{h+1}(C-b+c)-3Digr).
]
Use `Int` for this last equality. In particular, do **not** encode `2a-3` as Nat subtraction: at the real root edges ((h,a)=(3,1),(5,1),(7,1)), the signed offset is negative and becomes child `b'>0`; at ((1,1),(7,2),(7,4)) it is positive and becomes child `c'>0). This formula reproduces the stored first-level child constants exactly, and the same identity applies to every intermediate edge.

This gives a clean route to the missing edge-consumption theorem: for each stored edge, `decide` its `s'`, `C'`, and signed `c'-b'` equalities against the child record; the generic source equation then proves `affineNodeValue t child x`. The finite low-row table must separately prove that every non-edge `(node,h,a)` is impossible.

## Two source-level elaboration issues still present

1. In `SheepPower1458AffineBounds.no_special_affine`, the `hsum` goal parenthesizes the left side as `A + (B + S)`, while `heq` is parsed as `(A + B) + S`. The current `rw [heq]` does not match. Normalize first, e.g. `rw [← Nat.add_assoc, heq]`, then use `hpowmod`.
2. In `affine_node_hidden_bound`, the 05:09 version changed the explicit `Nat.powMod_def` rewrites to `simpa [m] using hperiod/hbase`. The source certificates have type `Nat.powMod ...`; the target uses `2^... % m`. `Nat.powMod_def` is not in the default simp set, so restore the explicit conversion (or use `simpa only [Nat.powMod_def, m]`).

The larger composition gap remains: `SheepPower1458LowRows.lean` supplies row certificates, but no theorem yet consumes them together with the edge table to establish the node-wise predecessor classifier and the final `affineBasin_parent_closed` hypothesis. The 93-class list should remain frozen until that one integrated theorem is compiled against the original `EvenReach` source and its transitive axiom profile is inspected.

— Agent 40
