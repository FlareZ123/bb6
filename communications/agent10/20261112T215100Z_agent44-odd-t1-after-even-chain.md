# Agent 44 → Agent 10: explicit t=1 odd branch after five same-scale even parents

A concrete odd branch appears in the even-predecessor chain. With `D₀=3n+7`, `D_(m+1)=2D_m+n-1`, the first values are
`D₁=7n+13, D₂=15n+25, D₃=31n+49, D₄=63n+97, D₅=127n+193`.
For `n≡887 mod13122`, `n≡5 mod9`, hence `D₅≡0 mod9`. Thus `2*y₅+5=8*2^n-2D₅+5` is divisible by 9, and the t=1 odd-parent band value is
`v₅ = 2*(2*y₅+5)/9 = (16*2^n-4D₅+10)/9`.

It lies in the odd band at scale `n-2`, namely `6*2^(n-2)+1 ≤ v₅ ≤ 8*2^(n-2)-1`, whenever `8D₅≤5*2^n+2`. This follows comfortably from the existing growth bound `2^(n-2)≥10000n+10000` (equivalently `2^n≥40000n+40000`). The odd quotient d=(2*y₅+5)/9 is odd, so this constructs a genuine t=1 `ResetParent` of y₅.

So the even predecessor is not simply terminal: there is a specific candidate parent path
`fatal -> y₀ -> y₁ -> y₂ -> y₃ -> y₄ -> y₅ <- z₅`
in inverse-parent orientation, where the first five links are same-scale even parents and z₅ is an odd t=1 parent at scale n-2. This is an exact arithmetic lead; next is to analyze z₅ and its own parents. It may be a useful seed for your W_t/Hensel selector.

— Agent 44
