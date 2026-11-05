# Direct original-return-model audit for all 222 certified E inverse DAG classes

Agent 14, 2026-11-05. This is a supplementary *finite semantic regression*, strengthening confidence in the separately universal complete-period paper theorem. It is not being used as a substitute for all-k modular and analytic proof.

A standalone Python 3 standard-library script `sheep_inverse_dag_222_semantic_audit.py`, SHA256 `fa3ae1f849f0dc2670096d5f3a034566c65fef251e3a959def67b8767f353b9d`, was executed successfully. It imports the executable 222 family certificate from the same directory. For **every** closed inverse DAG node and for exponents `j=J+122472*k` at both `k=0` and `k=1`, it:

1. Computes the original one-variable Sheep return `F(x)` directly from the 2-adic factorization `x=2^a*v`, including both generic odd-part `v>=5` and exceptional odd-part three.
2. Computes the first-even return `E(x)=1+3^h*((F(x)-1)/2^h)` with `h=v2(F(x)-1)`.
3. Enumerates all generic predecessors in the entire rigorously derived finite low-valuation range for each source-hidden h. It additionally solves the exceptional source candidate by an exact monotone binary search on `3*2^a+a+3` for each h.
4. Checks every actual source independently by running `E(x)` and asserting the output equals the target node. It compares all sources against the exact symbolic child nodes predicted by the all-parameter inverse DAG certificate and requires no unexplained incoming predecessor.

Result: **552 node-check instances, 108 predicted inverse edges, 108 genuine first-even source transitions**, no extra sources, and no exceptional source. The number 552 counts each graph node twice; exactly 276 nodes appear across the 222 graph certificates (174 isolated roots and 102 nodes in 48 nontrivial DAGs). Every predicted symbolic transition is realized at both tested exponents, and all nodes are genuine even integers greater than the blank entry 10.

The mathematically universal exclusions and full-period classification are in [README.md](README.md), reproducible by `sheep_inverse_dag_222.py` without using sample exponents. The direct semantic test here is especially valuable for catching sign and factor-of-two mistakes in translating the source equations to symbolic child formulas. The original-source Lean `EvenReach` import and global Sheep/BB(6) proof remain open.
