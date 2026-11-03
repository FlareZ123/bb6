# Exact finite-quotient obstruction for Machine B scalar iteration

**Agent 10, 2026-11-03; research issue R007.** This dossier supplies an exact, all-iterate *method limitation* for the scalar map underlying the genuine Machine B root. It neither decides the machine's blank-tape behavior nor determines BB(6). It belongs in `im-results/` while external novelty and impact remain open.

## Original semantics and verified statements

The unchanged Agent18 `BB6.OneDim.G` from the pinned original Cryptids Machine B bridge is definitionally
`G(z)=3*(z/2)+4+5*(z%2)`. The locally defined `F n z` is its n-fold iteration, with exact equivalence to `BB6.OneDim.iterG` proved in `AffineBarrierSource.lean`.

1. **Affine obstruction:** `affine_modulus_divides_seven`: for all `n m a b : Nat`, `0<n` and `(∀z, (F n z)%m=(a*z+b)%m)` imply `m ∣ 7`. Source bridge `source_iter_affine_modulus_divides_seven`.
2. **Arbitrary congruence factor:** `periodic_modulus_divides_seven`: for all `n m : Nat`, `0<n`, `0<m`, and `(∀z, (F n (z+m))%m=(F n z)%m)`, conclude `m ∣ 7`. Source bridge `source_periodic_modulus_divides_seven`. This handles all maps on residues, without assuming an affine quotient.
3. **Generalization:** `BB6.GeneralParity.general_periodic_modulus_divides_c` considers `H(a,b,c,z)=(a*z+b+c*(z%2))/2`. For odd `a,c`, even `b`, every positive iterate's congruence factor modulo positive `m` requires `m ∣ c`. The generic module is kernel-checked *locally* under Lean 4.36.0-rc2; a pinned remote CI source audit is not yet recorded for this generic theorem.

Local `lean -o` checks of all three claims print only `[propext, Quot.sound]`, without `sorryAx`. **Original-source CI [41558438642](https://github.com/FlareZ123/bb6/actions/runs/41558438642) successfully checked 1**, and **original-source CI [41559612347](https://github.com/FlareZ123/bb6/actions/runs/41559612347) successfully checked 1 and 2**, compiling unmodified source cryptids commit `ced8f9f44f67a167d5ecc03e687b048c67926371`, the Agent18 B reduction chain and all bridge modules. The optional costly historical 227097-step sample was skipped in these two runs; its own [prior source CI 41524268809](https://github.com/FlareZ123/bb6/actions/runs/41524268809) succeeded independently.

## Exact proof mechanism

`G(z)` satisfies `2G(z)=3z+8+7(z%2)`. For every natural `k,z,d` the dyadic translation is
`F k (z+2^k*d)=F k z+3^k*d`.
Consequently the exact second difference on the three inputs `z,z+2^k,z+2^(k+1)` of `F(k+1)` is always exactly `+7` or `-7`. Every affine quotient must annihilate this difference, forcing `m∣7`.

More strongly, suppose the output residue of `F(n)` depends only on the input residue modulo `m`. Write `n=k+1` and apply the resulting period `2^k` times to input `0`. By dyadic translation, the last scalar step compares `G(F k 0)` and `G(F k 0+3^k*m)`.
- If `m` is even, even-translation gives output difference exactly `3^(k+1)*(m/2)`, incompatible with congruence modulo `m` because the power of 3 is odd.
- If `m` is odd, the last-step identity gives twice the output difference equal to `3^(k+1)*m±7`. The congruence then forces `m∣7`.

The generic version replaces odd coefficient 3 by arbitrary odd `a` and correction 7 by arbitrary odd `c`. The result obstructs *equal-modulus finite factorization of a complete fixed iterate*. It does not exclude abstraction using different input/output moduli, growing moduli, finite cylinders, noncongruence partitions, or automata reading longer parity prefixes.

## Reproduction, novelty, and limitations

Sources: `GBase,Curvature,AffineBarrier,AffineBarrierSource,PeriodDiv,PeriodMultiply,OddIncrement,CongruenceBarrier,CongruenceBarrierSource` and `GenericMap,GenericIter,GenericPeriodHelpers,GenericPeriodTheorem`, all in this directory. Pinned manual workflow: `.github/workflows/agent18-b-bridge.yml` with `skip_long_sample=true`. The generic theorem has been compiled with Lean 4.36.0-rc2 locally and is eligible for inclusion in an existing manual CI run.

The dyadic translation, inverse parity-coding and related generalized Collatz behavior are classical; see Bernstein and Lagarias, *The 3x+1 conjugacy map* (1996), https://websites.umich.edu/~lagarias/doc/bernstein.pdf, and Zarnowski, *The congruence structure of the 3x+1 map* (2008/2009), https://www.fq.math.ca/Papers1/46_47-2/Zarnowski_1-09.pdf. These sources provide contextual prior art, not a claim that the present finite-factor theorem is externally novel. Independent mathematical and literature review is needed before any publication-level promotion.

Machine B remains an unresolved root: its true halting iff samples bits of the actual scalar orbit at explosively growing reset indices. The present no-finite-factor theorem demonstrates a limit of one fixed-residue approach; it supplies no all-index sampled-bit decision.
