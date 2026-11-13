# Exact n=887 odd-parent branch classes on the even spine

**Status: exact-integer census from the complete ResetParent equations.** The all-precision Hensel selectors identify the first-tier classes; the second-tier finite branch table below is an exact BigInt computation, not yet a standalone Lean theorem. The 1,319-state Lean reverse-cone certificate remains unverified by a successful source CI run.

## 1. Main-spine depth range

For n=887, the same-scale even spine has 876 states, indexed by m=0,…,875. Under the canonical-ray identity

2*y_m+5 = signedZ(887,m+1),

its depth range is j=1,…,876.

## 2. First-tier depth Hensel residues

Direct modular evaluation of the exact signedZ formula gives the unique depth residue R_k modulo 2·3^k for 3^(k+1) dividing signedZ(887,j):

| k | R_k | period 2·3^k |
|---:|---:|---:|
| 0 | 0 | 2 |
| 1 | 0 | 6 |
| 2 | 6 | 18 |
| 3 | 42 | 54 |
| 4 | 150 | 162 |
| 5 | 474 | 486 |
| 6 | 474 | 1,458 |
| 7 | 3,390 | 4,374 |
| 8 | 3,390 | 13,122 |
| 9 | 3,390 | 39,366 |

The exact Lean theorem CascadeRayDepthResidue.depthResidue_iff states the general all-precision criterion. The residue values above are its n=887 evaluations; the selector's source-check status must be assessed separately.

## 3. Exact first-tier ResetParent band census

Enumerating every odd ResetParent exponent t allowed by 3^(t+1) dividing signedZ(887,j), then applying the exact odd-band condition, gives exactly:

| odd exponent t | depth class j | count on 1≤j≤876 | odd-band scale k |
|---:|---|---:|---:|
| 1 | j ≡ 0 (mod 6) | 145 | 885 = n−2 |
| 3 | j ≡ 42 (mod 54) | 16 | 884 = n−3 |
| 6 | j = 474 (mod 1458) | 1 | 882 = n−5 |

No other t gives an odd ResetParent on this n=887 main spine. In particular, t=0,2,4,5 have Hensel divisibility classes, but their quotients lie in dyadic gaps rather than odd image bands; the first t=7,8,9 Hensel class begins at j=3,390, outside this spine.

The branch counts are 145+16+1=162, exactly the odd-parent edges leaving the main spine in the generated 1,319-state reverse cone.

## 4. Corrected second-level closure of the t=3 and t=6 arms

The earlier version of this note incorrectly reported four even parents at j=150,312,636,798 and no odd parents among the t=3 roots. Direct recomputation from both complete ResetParent equations gives the following corrected census.

For each t=3 root at j=42+54r, where 0≤r≤15:

- Exactly five roots have one further parent: j=96,258,420,582,744, equivalently j≡96 (mod 162).
- Each of these five has exactly one additional odd parent, with exponent t'=0 and odd-band scale k=883=n−4.
- Each of those five additional parent states is parent-free.
- The other eleven t=3 roots have no further ResetParent.
- No t=3 root has an even parent.

The second-level parent formula is explicit. Write Z=signedZ(887,j), d=Z/81 and

h₃(j)=16d−2^887−889.

At the five listed depths, e=(2h₃(j)+5)/3 is odd and lies in the k=883 odd band. The additional parent is

g₃(j)=2e−2^886−888.

The exact parent enumeration finds no ResetParent of any of these five g₃ states. There is a useful boundary case at j=420: a further power-of-three divisibility candidate exists, but its odd-band quotient lies in a dyadic gap and therefore is not a source parent.

This nested numerator is already covered by Agent 7's translated Hensel tower; do not build a duplicate selector. For general n in the surviving sectors, if Z=signedZ(n,j), h₃=16(Z/81)−2^n−n−2 and C=2^(n+1)+2n−1, then
81(2h₃+5)=32Z−81C.
With c_n=38C mod 81 and offset_n=81c_n, this gives
81(2h₃+5) ≡ 32(Z−offset_n) (mod 3^8).
Since 32 is a unit modulo every power of 3, the existing translatedDepthResidue selector for Z−offset_n is exactly the selector for the nested odd-parent valuations of h₃. At n=887, its precision-3^5 class is j≡96 (mod 162), giving the five t'=0 parents above; its precision-3^6 class is j≡420 (mod 486), but the t'=1 odd-band test fails; its precision-3^7 class is j≡1392 (mod 1458), and its precision-3^8 class is j≡4308 (mod 4374), both outside the n=887 spine. See ../agent7-fatal-density/TranslatedDepthResidue.lean and ../agent10-cascade/TThreeHighGateResidue.md for the source-checked translated tower and the high-q specialization.

The t=6 root at j=474 has exactly one further parent, an even parent at scale k=882=n−5. That parent is itself parent-free. The t=6 root has no odd parent.

Thus the t=3 side subtrees have maximum depth two, with five one-edge odd continuations; the t=6 side subtree has one one-edge even continuation. The corrected side-branch census is still a finite n=887 statement, not a uniform theorem for all n≡887 (mod 13122).

## 5. Second-tier t=1 gate on the even-parent arm

For every one of the 145 t=1 branches, the actual even parent w of its odd predecessor satisfies the exact source identity

T_887(j)=16·signedZ(887,j)−9(12·2^887+6·887+3)=9(2w+5).

The second-tier Hensel residues and exact valuation census are recorded in ../agent10-cascade/TWO-TIER-DEPTH-887-RESIDUES.md. On the relevant j range, the 17 depths with 3^4 dividing T are exactly j≡6 (mod 54):

6, 60, 114, 168, 222, 276, 330, 384, 438, 492, 546, 600, 654, 708, 762, 816, 870.

The exact valuations among these are:

- v₃(T)=4: 60, 114, 222, 276, 384, 438, 546, 600, 708, 762, 870;
- v₃(T)=5: 6, 330, 492, 816;
- v₃(T)=6: 654;
- v₃(T)=7: 168.

Thus only 17 of the 145 t=1 branches can continue through a second-tier odd-parent divisibility gate. The nested Hensel selectors classify further valuations, but exact source-band tests are still required to identify actual parent edges.

## 6. Parallel direct-odd-parent gate from the t=1 state

For each t=1 branch at depth j, let p=2^(n−2). Its odd predecessor is

z₀(n,j)=(56p−n−15−4·2^(j+1)(2n+3))/9.

The exact numerator controlling odd parents of z₀ is

U_n(j)=9(2z₀(n,j)+5)=112p−2n+15−2^(j+4)(2n+3).

This is a second arm, distinct from T_n(j)=9(2z₁+5), the numerator for the even parent z₁ of z₀. For n=887, among the 145 t=1 spine depths, exact ResetParent enumeration finds:

- t'=2 odd parents of z₀ at exactly j=162,324,486,648,810 (j≡0 mod162), with v₃(U)=5 and odd-band scale k=883=n−4;
- an additional t'=4 odd parent at j=486, where v₃(U)=7 and the odd-band scale is k=882=n−5.

No other direct odd parent of z₀ occurs among these 145 states. Thus the t=1 branch has two parallel second-tier gates: T on the z₁ arm and U on the z₀ arm. The five U-gated depths are separate from the 17 T-gated depths; both must be included in a complete closure proof.

U_n(j) is another affine-exponential numerator in j, so it should admit a Hensel depth selector of the same type as depthResidue and twoTierDepthResidue. The observed classes are consistent with 3^5 dividing U at j≡0 (mod 162) and the 3^7 refinement at j≡486 (mod 1458). A general selector proof and the source-band implications remain to be formalized.

## 7. What is structurally reduced

The n=887 main-spine odd-parent set is described by three Hensel depth classes, with exact dyadic scales. The t=3 and t=6 arms have the corrected shallow continuations above. The difficult recursive structure is concentrated in the t=1 arms and their parallel T/U gates.

The full reverse-cone generator reports 1,319 states, 1,318 edges, 181 leaves, and no merges. The 1,319 hexadecimal entries in EvenPre887Cone.lean match an independent exact-integer reimplementation of the two ResetParent equations. This comparison checks the generated list against the same mathematical grammar; it is not a Lean proof. The Lean closed-cone certificate still requires a successful source CI run.

The remaining proof work is to:

1. formalize the n=887 band/gap implications for t=0,1,2,3,4,5,6 and the absence of t≥7 in this finite depth range;
2. compose the T-selector with the exact source-parent equations for all 145 t=1 branches;
3. classify the nested odd/even branches at the 17 second-tier depths and the five U-gated depths;
4. prove the terminal status of the corrected t=3 and t=6 side branches in Lean;
5. establish the exact closed-cone certificate against the original source dependencies.

Do not infer a uniform n-family from this finite census. For larger n, the first t=7 and t=8 depth classes enter the main spine; higher Hensel digits eventually matter.

— Agent 7


## 8. Compact source certificate and verification status

The finite side-branch census has a compact Lean formalization on branch agent7-887-even-parent:

- EvenPre887T3T6.lean defines the 17 first-tier t=3/t=6 roots and six second-tier children.
- It proves the 17 exact spine-to-parent witnesses using parentsFast_iff.
- It proves the exact parent lists for all 16 t=3 roots and the t=6 root, terminality of all six children, nodup and length 23, and a 23-state closedCertFast certificate.
- sideCone_no_root then excludes all 23 states from ReachC((2,0),·) using closedCertFast_excludes. The finite checks use by decide.

The large 1,319-state certificate has been split into EvenPre887ConeOnly.lean (only ClosedCertFast dependency) and a thin EvenPre887Cone.lean wrapper that imports FeederExceptional887. A manual-only workflow, agent7-887-cone-only.yml, compiles the compact 23-state theorem first and then the large cone; the full fan-in workflow also compiles the compact theorem immediately after ClosedCertFast. The workflow has no push or pull-request trigger.

Latest branch revision at this note update: 290f5b0550b66d70c618d22b89e236a8deadcf08. This source formalization is pending CI dispatch and a successful Lean 4.36.0-rc2 run. Do not treat the Lean declarations as verified until the workflow reports successful compilation and the printed axiom lists are reviewed.


## 9. Integration with the t=1 z1/z2 branch

Agent 10's z1 in Z1UniqueParent887.lean is exactly the z1 already defined in EvenParent887.lean:

z1(n)=2·z0(n)−8·2^(n−2)−(n−2),

and the existing identity is

9·z1(n)=40·2^(n−2)−2059n−3084.

Thus Agent 10's quotient coordinate A(p,n)/9, with p=2^(n−2), is the same Nat state. Its T(p,n)=80p−4118n−6123 is exactly 9(2·z1+5), and its z2 formula is the next source parent of that same state.

At n=887, y5, z0, z1, and z2 all occur in the 1,319-state EvenPre887ConeOnly list. An exact-integer parent-tree audit finds an 11-state backward-closed subtree rooted at z1: z1 has the unique parent z2; z2 has two parents (one even, one odd t=1); the remaining tree has three terminal leaves. This connects Agent 10's uniform z1-parent theorem to a concrete branch of the fixed n=887 cone.

The finite subtree is formalized in Z1Z2Cone887.lean on branch agent7-887-even-parent. It proves the complete 11-node parent table, z1's unique parent z2, and z1Cone_no_root using closedCertFast and by decide. It is a finite n=887 result, not a replacement for Agent 10's uniform theorem. The t=3/t=6 side cone is a separate branch. The compact z1/z2 module is pending CI, like the other new compact certificates.

Latest branch revision at this note update: e6e47a98aad8de603d0f50a94d42fb304359b2bf.


## 10. Uniform U/Q odd-parent band envelope

The direct-odd-parent numerator on a first-tier t=1 spine branch is
`U=9(2z₀+5)`, with the exact affine identity
`U + 2n + 2^(j+4)(2n+3) = 112·2^(n−2)+15`.
If the physical state z₀ lies in its source even band
`6·2^(n−2)−1 ≤ z₀ ≤ 8·2^(n−2)−3`, these two identities imply the stronger, uniform envelope

`27·2^n < U < 28·2^n`.

For an odd ResetParent with exponent t′ and odd quotient d,
`2z₀+5=3^(t′+1)d`, so `U=3^(t′+3)d` and the actual odd-band argument is `2^t′d`. The envelope now gives the following exact source-band restrictions, uniformly in n and j whenever the displayed affine identity and source-band premise hold:

| t′ | Consequence |
|---:|---|
| 0, 1, 3, 5, 6, 8, 10 | The odd-band argument lies strictly in a dyadic gap; these exponents are impossible |
| 2 | Any odd parent is forced to scale n−4 |
| 4 | Any odd parent is forced to scale n−5 |
| 7 | Any odd parent is forced to scale n−7 |
| 9 | Any odd parent is forced to scale n−8 |

This is a uniform band-envelope theorem, not a complete parent census: exponents t′≥11 are not classified here, and the hypotheses still need to be instantiated from the full first-tier t=1 ray construction. In particular, the Hensel selector remains the separate source of divisibility/index restrictions; this result deliberately does not duplicate Agent 44's Q/U selector work.

The Lean module `UParentBandEnvelope.lean` on branch `agent7-887-even-parent` contains the arithmetic proof and a wrapper that consumes the exact `CascadeResetInverse.ResetParent` disjunction, preserving its even arm and strengthening every odd arm. It imports `FirstInverseComplete`. The arithmetic and source-shaped wrapper compiled locally against a stub with the exact checked-in ResetParent signature; **that is not actual-source CI verification**. The focused manual-only workflow `agent7-u-parent-band.yml` compiles the original dependency chain through `FirstInverseComplete` and then the new module. Await a successful run and inspect all three `#print axioms` outputs before treating the source wrapper as verified.

The new envelope is useful beyond the fixed n=887 census: it rules out the same seven exponents and fixes the same four band scales for every first-tier t=1 branch satisfying the exact formula and band hypotheses. It does not imply that only t′=2 or 4 can occur at larger n; higher admissible exponents such as 7 and 9 are already retained explicitly.
