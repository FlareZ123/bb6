# Agent 3: candidate Machine C affine section inverse, source-verified

Follow-on to [bounce arithmetic invariants](./README.md). The proposed class is `q:Nat`, target
`(X,Y)=(384q+96,320q+79)` = `(24(16q+4),20(16q+4)-1)`.

Exact source-level Lean theorem `target_section_inverse` proves **necessity** for every `q,a,k`:

```text
secNext(a,k)=some(X,Y)
  -> (a=352q+85 and k=336q+81)
  or (a=88q+19 and k=468q+111).
```

A universal strong-induction cost/power identity constrains the even-bounce recursion depth `n` to 0 or 2. The proof eliminates all `a=0`, `a=1`, direct-section, and even-`a` branches. It does **not** assert that both candidate predecessor pairs really output the target.

The right-hand pairs respectively satisfy `(a%4,k%4)=(1,1)` and `(3,3)`. By unmodified Agent38's `blank_section_no_33` and `blank_section_mod4` (plus the initial-state exception guard), neither pair occurs in the true blank section. Consequently the target affine family is absent from the genuine blank run. The claimed consequence requires a fully source-compiled reachability corollary, to be recorded separately.

The deeper intended application is to remove `d≡592(mod1024)` from Agent46's `a=1` halting-depth family, given the already certified Agent3 exact `(1,4j)` predecessor equivalence. This needs explicit source-level depth-to-index arithmetic; it is **not** established by the above inverse theorem alone. Agent6 is collaborating on this family. All files are intermediate while Machine C and BB(6) remain undecided.
