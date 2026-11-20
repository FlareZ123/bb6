# Agent 17 update: preferred two-node t=8 inverse-tree progression

The earlier (t\equiv1\pmod{32,526,940,446,000}) candidate is superseded as the preferred target by this two-node class.

```lean
theorem sheep_seventh_t8_unreachable (k : Nat) :
  ¬ SheepEven.EvenReach 10
      (2^(1458*(8 + 10475665200*k)))
```

Here (T=10,475,665,200=2^4\cdot3^4\cdot5^2\cdot7\cdot11\cdot13\cdot17\cdot19). Equivalently (j=11,664+15,273,519,861,600k).

For (t\equiv8\pmod{1260}), the exact first-parent census has exactly one generic hit: (h=7,a=4). Its source is
[
x=16v,\quad 72,171v+11,191=2^{1458t+8},
]
so the sole intermediate node is
[
Y_1(t)=\frac{2^{1458t+12}-179,056}{72,171}.
]
At t=8, (v_3(Y_1-1)=0). The complete generic-parent census for this node (h=0, a<22) has no hit; all a>=22 are excluded by your signed-power gap. The exceptional source is excluded at both nodes by the (2^a\mid L(a))/size split.

The exact certificate computes 91 modular periods and two 3-adic valuation periods. The tree-period LCM is 2,095,133,040; the LCM of the 28 previous E-cone periods is 1,178,100; their LCM is (T=10,475,665,200). It has two nodes, one edge, no special parents, and the second node is a leaf.

Artifacts:
- `im-results/agent17-sheep-power1458/inverse_tree_t8_certificate.py`
- `im-results/agent17-sheep-power1458/T8-INVERSE-TREE.md`
- the earlier, larger t=1 candidate remains in `INVERSE-TREE-PROGRESSION.md`.

Please prioritize independent checking of the t=8 derivation and, if sound, formalization against the original source modules. The local Python/shell tools return platform ClientError for me, so I cannot perform the required local Lean preflight in this invocation. Do not treat the JS arithmetic as a proof; keep this in im-results pending Lean and axiom audit.
