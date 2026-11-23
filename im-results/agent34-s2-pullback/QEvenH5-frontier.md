# q-even hcong=5 frontier (exploratory; not a proved exclusion)

The q-even parent parameterization is
`u = 32*z - 7*t - 10`, `v = 12 + 11*t - 32*z`, with
`7*t+10 ≤ 32*z ≤ 12+11*t`. Its existing excluded lift is
`(2*t-z) % 8 = 1), equivalently
`53*u+57*v ≡ 282 (mod 1024)`.

The adjacent lift `(2*t-z) % 8 = 5` gives
`53*u+57*v ≡ 794 (mod 1024)`. Pulling this through the same high-stop identity gives the candidate parameter cylinder
`j % 512 = 319` and
`m % 1048576 = (7210 + 337408*(j/512)) % 1048576`.
The exact equivalence is now stated as `q_even_h5_parameter_pullback_iff` in `CSixSeventhS2Pullback.lean`: `171*m+879873 ≡ 49*j (mod 1048576)` iff the displayed m-residue cylinder. This declaration still awaits a fresh original-source CI run. It is disjoint from the existing q-even hcong=1 cylinder (the constants differ by 524288 modulo 1048576) and from S2 (their residues differ by 65536 modulo 131072). Its reduction modulo 16384 is the same as the existing S2/q-even cylinders, so it is not removed by the old S3 residue-zero exclusion.

The exact `q_even_R_parents` classification still gives the direct parent P and odd-bounce parent Q on this lift. The direct-parent exclusion appears to use only the mod-4 consequence of hcong=1, so hcong=5 may be enough there; this has not yet been formalized. The bounce-parent proof does not transfer: hcong=1 gives the intermediate right coordinate 4 mod 8 and a `blank_no_odd_sum_one` contradiction, whereas hcong=5 gives right coordinate 0 mod 8. Its first six-even-right inverse is even/odd with sum 3 mod 4; the existing odd-image criterion permits that sector. Some further z residues trigger an even-seven normalization edge, but no all-time blank-root exclusion has been established.

`QEvenH5Probe.lean` and the optional `s2_qeven_h5_probe` workflow input evaluate the exact `valSixMixedRootDecision` on representative hcong=1 and hcong=5 parent states. The probe has not yet been run. A positive result would be a source-root witness for that sample; a negative result would only be computational evidence for that sample, not a family theorem.
