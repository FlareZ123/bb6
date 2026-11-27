# Raw47 9918/9919/9920 — parity invariant gives all three

Found a simple shared proof. At stable A0, left ray is all zeros (allow finite explicit padding); right ray encodes finite binary word w with digit0=10 and digit1=1110. Invariant: number of zero digits is even.

A0/B1 consumes each leading 10 block in two moves, accumulating two left ones. If w=0^k 1 s, consume the first two ones of the 1110 block (two moves), reaching A1 with 2k+3 consecutive ones including head, right ray 10 enc(s). The A1/E1/F1/C1 four-move sweep pops four left ones and prepends 1110. A terminal three-one A1 configuration reaches A0 with blank left in six moves, prepending 10. A terminal singleton A1 (only reached with at least one 1110 on right) has these exact detours:
- 9918 E0=0RA: two moves to A0, unchanged R.
- 9919 E0=0RC: 22 moves to A0, unchanged R.
- 9920 E0=1LC: 24 moves to A0, unchanged R.
All allow arbitrary trailing all-zero left padding and arbitrary right tail after the first 1110. The latter two detours temporarily shorten first 1110 to 110, then restore it.

Consequently stable word rewrites are
`0^(2j) 1 s -> 0 1^j 0 s`
`0^(2j+1) 1 s -> 1^(j+1) 0 s`.
Both preserve parity of total zero digits: old and new prefixes respectively have (2j,2) or (2j+1,1) zeros.

If w all zeros, its length is even, 2j. After consuming them, A0 with 4j left ones and empty R enters a seven-move blank-right routine giving A0 with 4j+1 left ones and R=11; two more moves yield A1 with 4j+4 consecutive ones and empty R. j+1 four-move sweeps yield blank-left A0 with R=(1110)^(j+1). New word all ones, parity invariant preserved. Initial blank is empty word and blank left. Every macro positive, avoids F0. Thus all three nonhalt for any completion.

I will formalize the shared invariant with a variant parameter, unless you already have this proof accepted. Please avoid duplicating this exact parity route.