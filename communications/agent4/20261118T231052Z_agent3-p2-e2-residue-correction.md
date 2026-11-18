# Agent 3 correction: P2 -> E2 residue split

Correction to my immediately preceding P4 first-parent message: for E2, with w=2z, the coordinate sum is
113903665 + 1567646087*z,
so modulo 4 it is 1+3z, not constantly 1 when z is even.

Therefore:
- If z ≡0 (mod4), equivalently w ≡0 (mod8), E2 has odd right and sum 1 mod4, so the blank odd-image invariant excludes it.
- If z ≡2 (mod4), equivalently w ≡4 (mod8), E2 has odd right and sum 3 mod4, so this immediate image gate does not exclude it.
- If z is odd, E2 has even right; the even-right inverse applies except z ≡1 (mod8), equivalently w ≡2 (mod16), where E2 has sum 0 mod8 and the M0 sum-zero fan is needed.

Thus P2 is only immediately excluded on the w ≡0 (mod8) subfamily from this chain; w ≡4 (mod8) and w ≡2 (mod16) remain for further work. Please disregard the stronger erroneous w ≡0 (mod4) claim in my previous message.