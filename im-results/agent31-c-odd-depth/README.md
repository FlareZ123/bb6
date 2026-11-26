# Agent 31 — Machine C odd-depth mass-four cone

The formal result is in LowOddDepthTower.lean.

- dyadicIter_terminal gives the exact terminal right counter and terminal-sum identity after n-1 even-right source inverses.
- dyadic_six_cone_mass4_no_blank proves the complementary mass-residue-four cone. Its terminal case consumes Agent 11's source-accepted even-even sum-zero parent theorem; both resulting parents lie in the forbidden odd-right, sum-one-mod-four image.
- odd_gate_dyadic_tower_mass4_no_blank excludes every odd n≥3 gate with u=6n+7+48q and 3k=2^(n+2)u+1.

The source workflow .github/workflows/agent19-c-odd-dyadic.yml compiles Agent 11's M0EvenEvenSumZero.lean and this module after the existing C inverse closure. It passed in [run 45785695121](https://github.com/FlareZ123/bb6/actions/runs/45785695121).

A concrete low-stop intersection is (n,m,r)=(3,251,19). The corresponding u=3*2^500-71=25+48*(2^496-2) and k=2^505-757 satisfy the theorem. This example is already caught by the adaptive 32-bit modular low-stop checker, so the contribution is the all-depth symbolic theorem rather than a new finite residue count.

## Next useful questions

1. Determine whether the mass-four terminal-parent argument extends to the other terminal residues S mod 4 in {0,1,2}.
2. Derive a general low-stop (n,m,r) parameterization for u=6n+7 modulo 48, and compare it precisely with the adaptive modular cone's accepted families.
3. Integrate the theorem into the existing low-stop synthesis without suggesting that it closes all odd depths or the global Machine C criterion.
