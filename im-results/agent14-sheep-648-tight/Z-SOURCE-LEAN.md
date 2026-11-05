# Locally kernel-certified complete original-source-shaped Z leaf

Agent 14, 2026-11-05 19:32 UTC. Companion to [sevenfold tightened 648 family](README.md). **New formal mathematical result:** the additional r=2 node `Z=(2^(j+10)-16576)/3483`, where `j=35640+122472k`, has no incoming even first-return edge under the two exact source inverse forms for any natural k.

The terminal locally Lean 4.36.0-rc2-compiled theorem is `SheepZSourceCases.no_z_source_cases`. For every natural `k,x,y` satisfying

```
3483*y+16576=2^(35650+122472*k)
```

the theorem rules out the exact disjunction in `SheepEvenSourceAlgebra.original_even_edge_inverse_cases`, specialized to `d=3483,c=16576,n=35650+122472*k`. The generic source case retains all `a>=1,h,v,u` with `v>=5`, oddness, source equality, target equality, and its full

```
(3483*3^h)*(2^(a+1)+1)*v+2*a*(3483*3^h)+
  2^(h+1)*3483+2^(h+1)*16576 =
  2^((35650+122472*k)+h+1)+3*(3483*3^h)
```

equation. The exceptional odd-part-three source case retains all its original source equations. The source-algebra theorem was already original-machine certified separately. **The terminal Z theorem itself has not yet been compiled in the same original-Cryptids CI import chain**, so do not report the Z node as a newly certified unchanged-source theorem.

## Locally compiled Lean proof chain

- `SheepZHighH.z_hidden_zero` proves `h=0` uniformly, using the exact inequivalent residues `2^35650 mod10449=6127` versus `20059 mod10449=9610`, and `2^122472 mod10449=1`; axioms `[propext, Quot.sound]`.
- `SheepZLow01/07/12.lean` proves all 17 universal low-generic congruence exclusions for valuations `a=1,...,17`, covering all 113 complete-order period representatives. All have `[propext, Quot.sound]`.
- `SheepZSourceLow01/07/12.lean` transports each of those 17 congruence exclusions to the **full exact generic source equality** with the correct additive offsets; all 17 universally quantified source-shaped theorems compile with `[propext, Quot.sound]`. For `a=1,2`, the quotient compensation is respectively `t=3,2`, accounting for a signed remainder larger than the modulus; for larger a it is `t=1`. This is important for soundness.
- `SheepZGenericHigh.no_z_generic_high` proves the exact generic source equation impossible for **all `a>=18`** by applying the reusable `SheepGenericSourceHigh.no_generic_source_eq` to `D=3483,Q=20059,C=-16576` and the existing odd-gap theorem; axioms `[propext, Classical.choice, Quot.sound]`.
- `SheepZSpecial.no_z_special` proves the entire special odd-part-three equation impossible for **all a and k**, with `A=10449,D=3483,C=27025,e=13,L=5935,t0=5`; axioms `[propext, Quot.sound]`.
- `SheepZNoGeneric.no_z_generic_all`, `SheepZSourceLeaf.no_z_generic_source`, `SheepZSourceLeaf.no_z_special_source`, and terminal `SheepZSourceCases.no_z_source_cases` perform the finite cases and original-source-expression normalization. The terminal theorem's complete axiom audit is `[propext, Classical.choice, Quot.sound]`, with **no `sorryAx`**.

All statements were compiled locally in Lean 4.36.0-rc2 from exact source in the accompanying standalone archive `Sheep648ZLeanCertificate.zip`, SHA256 `0e391beb4300e40535195ffd30388a21ee78a91eac1379c3758ffec70fb832af`, which is a user-visible artifact of this invocation. The archive includes 18 Lean modules, their local generators, and the all-seven-residue Python arithmetic certificate. Upload of source files to the shared repository through the available connector was blocked; this report preserves the precise theorem signature and source-transfer target without inventing a CI result.

## Remaining goal

To promote this Z leaf to an unchanged-original-machine Lean theorem, import the pinned original `EvenEdge` module, `SheepEvenSourceAlgebra.original_even_edge_inverse_cases`, and the locally checked `SheepZSourceCases.no_z_source_cases` into one source workflow. Then complete the other six genuinely new residues in the sevenfold family, using the established source DAG induction. A full Sheep nonhalting decision and BB(6) remain open.