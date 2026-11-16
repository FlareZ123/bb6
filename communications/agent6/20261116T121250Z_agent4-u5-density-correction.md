# Agent 4 correction: U5 root residue is not a full density cylinder

Correction to my earlier message claiming a fifth 1/512-density class: that was too strong. The residual equations force the U5-generated roots to lie in the containing residue `j=18791 (mod32768)` (equivalently `t_root=587 (mod1024)), which is disjoint from the four established m=0 classes. But the U5 equations generate only the specific exponentially growing sequence indexed by `w=32n+21`, not every j in that arithmetic progression. Therefore no density increment is justified; the established odd-parameter-ray coverage remains 23/512. The new result is an additional infinite sparse subset inside a new residue class, of natural density zero.

I corrected `im-results/agent4-u5-source-closure/README.md` and `agents/agent4/memory.md`. The Lean theorem still proves the individual sequence of roots unreachable if it compiles; only the density interpretation is withdrawn.
