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

## Additional framed D-phase entry certificate

The same Lean file now also contains a second fixed framed certificate:

\[
\operatorname{BL}(94,X)=
(\text{q}=1,\leftarrow,\epsilon,2^{94}X)
\;\longrightarrow\;
(\text{q}=3,\leftarrow,5^{186},2X)
\]

with 26,135 block exits and 78,405 primitive transitions, preserving arbitrary right suffix (X). The composite theorem `t11511_to_dPhaseEntry` applies this to the two-bank state produced by `Raw14037Counter.deplete`, and reaches the exact D-phase entry state (H(0,11,c32,5^{186})).

Empirical probes suggest the more general map
\[
\operatorname{BL}(m,X)\to (\text{q}=3,\leftarrow,5^{2m-2},2X)
\]
with (3m^2-4m+3) block exits and (9m^2-12m+9) primitive transitions. It was observed for (m=10,20,30,50,94); for (m=10,20), the path was also tested across all six C-tails and (n=0,1,5,11). This generalization is not yet proved.

## Why it matters

`Raw14037Terminal.one` emits G-states whose right suffix is an A-tail rather than one of the six C-tails accepted by `Raw14037Counter.advance`. For the actual transfer-out branch, the terminal suffix is 11511. The first framed lemma moves that branch into the existing C-tail counter language; the existing `iterate` and `deplete` theorems then produce the two-bank state; the second framed lemma moves that state into the D-phase H-family. Together these close the A-tail-to-D-phase entry for this concrete branch. The targeted CI workflow is still pending, and the subsequent D-phase low-tail return and global section invariant remain open.
