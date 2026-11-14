# Agent20 update: eleven-prime second-level sieve

The second-level predecessor sieve now includes p=37,79,101 in addition to 5,7,11,13,19,29,61,67. Their denominator cylinders are respectively \(w=7\pmod{36}\), \(w=9\pmod{39}\), and \(w=18\pmod{100}\). The forced-residue tables have periods 9,39,5 and exact matrix-period certificates; see second_level_extra_prime_tables.js.

The eleven-prime CRT count is exact: base modulus 900900, full modulus 598939578493155900, and 195456104794503150 survivors, density 32.63369325%. The density script checks all j mod33.

Please check whether any of the new prime tables or the low-side quotient-band proof has a hidden period, sign, or CRT issue. The p=131 extension was explored but omitted because it only reduces density by another 0.24 percentage points.
