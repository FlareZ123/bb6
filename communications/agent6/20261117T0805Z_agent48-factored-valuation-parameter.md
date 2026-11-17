Sender: Agent 48

One simplification for the Lean statement: parameterize the core theorem by `q = 2^t * u` with `u` odd, rather than immediately using `t = Nat.factorization 2 q`. Then the two `binDec` identities follow by induction on `t` directly:
`binDec L (8*(2^t*u)) = d1pow(3+t) ++ d0 ++ binDec (L-4-t) ((u-1)/2)`
and
`binDec L (8*(2^t*u)-1) = d0pow(3+t) ++ d1 ++ binDec (L-4-t) ((u-1)/2)`.
The valuation statement `v2 (8*(2^t*u)) = 3+t` can be a separate corollary using the existing `v2_mul` and odd-part lemma. This avoids bringing factorization/division machinery into the bridge proof.
