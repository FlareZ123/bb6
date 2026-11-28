# Raw37 A-tail to C-tail bridge

## Lean certificate authored; CI verification pending

The new Lean file `Raw14037ATailBridge.lean` contains a framed certificate for the transition

[
G(15,3^{70}X,11511)\;\longrightarrow\;G(25,3^{65}X,31)
]

for arbitrary untouched left suffix (X). The proposed certificate uses 943 block exits and 2,629 primitive transitions; the targeted workflow has been added but has not yet completed. It is stated over the common base table, not the M37 completion, so it does not depend on sibling-specific rows. A separate table-extension lemma is still needed to state the corresponding reachability theorem for each completed sibling.

The proof uses `Raw140Framed.execute_sound` with an open left context. The computed path preserves the suffix (X); a simulator probe with opaque block 8 confirms it is not read. For the exact (v=15,w=65,X=[2]) path, transition counts by state/bit are:

- A: 8 reads of bit 0, **0** reads of bit 1;
- F: **0** reads of either bit.

Thus none of the variant-specific A1/F0/F1 rows is used.

## Empirical generalization (not yet proved)

Block simulation supports the broader family

[
G(v,3^{w+5}X,11511)\;\longrightarrow\;G(v+10,3^wX,31)
]

with (40v+343) block exits and (110v+979) primitive transitions. Probes covered (v=0,1,2,3,5,10,12,15,20), several (w), and different suffixes (X). This affine generalization remains a conjecture until a parameterized Lean proof is supplied.

Two further empirical A-tail conversions were observed:

- (G(v,3^{w+8}X,152)\to G(v+13,3^wX,31)), with (64v+643) block exits and (176v+1809) primitive transitions;
- (G(v,3^{w+8}X,1121)\to G(v+13,3^wX,31)), with (64v+639) block exits and (176v+1799) primitive transitions.

These are simulation observations only.

## Why it matters

`Raw14037Terminal.one` emits G-states whose right suffix is an A-tail rather than one of the six C-tails accepted by `Raw14037Counter.advance`. For the actual transfer-out branch, the terminal suffix is 11511. This lemma moves that branch into the existing C-tail counter language, after which `Raw14037Counter.iterate` and `deplete` can be applied. It closes one explicit interface gap; it does not by itself prove a complete return or nonhalting.
