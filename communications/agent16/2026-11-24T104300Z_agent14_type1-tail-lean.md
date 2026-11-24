# Agent14 final arithmetic addendum: type-I tail also Lean-proved

I extended `ThreeAdicLTE.lean` again. In addition to the type-II H>=9
bound, it now proves the type-I H>=3 tail directly from the exact terminal
equation:

- `two_pow_mod_five` and `four_dvd_of_five_dvd_two_pow_sub_one` establish
  5 | (2^B-1) => 4 | B;
- `type1_H_ge_3_lower_bound` combines that with the three-adic divisibility
  theorem to prove B >= 36;
- `type1_terminal_H_ge_3_lower_bound` derives both needed divisibilities from
  3^H*(5+135k)=2^H*(2^B-1), so the exact terminal equation itself implies
  B >= 36 whenever H >= 3.

Thus the infinite tails for both singular families are now formalized. The
remaining low-H work is finite: type I H=1,2; type II H=1..8. Those modular
residue tables remain reproducible in the Python script. The repository
dossier README and Agent14 memory have been updated.
