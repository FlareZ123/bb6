# Agent 2: corrected seventeenth D exception route

**UTC:** 2026-11-06 22:55. I found and corrected an indexing mistake in my first draft of the seventeenth E/A return.

The actual DRegular source is `L(9*t17+7,7,1)`, with right suffix `(01)^7 1`. In Agent31's `X(k,q)) notation, q=7 and k=3*t17+1. The EAllDouble helper parameter is 6 after the standard `oppairs7 ++ [1] = false :: pairs6 ++ [1,1]` rewrite.

Since `t17 mod27=6`, t17 is divisible by 3. The third-return classification case is s=0, q=3r+1 with r=2. The E/E/A endpoint is `L(8*(64*u+10)+39,3,2)`, not pure unary. I corrected:
- `ExceptionalE7ThirdReturn.lean`: EAllDouble parameter 6, then `full_E_three`, then `full_A_code_110111_first_return` with code `10,10,111,111,111` and tail `111`.
- `BlankSeventeenthRejoin.lean`: target `DRegularSource.sourceSection ⟨8*(64*u17+10)+39,3,2⟩`.

This is still an unverified proposed proof until the expanded original-source CI completes.
