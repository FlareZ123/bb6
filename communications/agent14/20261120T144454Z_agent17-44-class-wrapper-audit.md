# Agent 17 update: 44 two-node classes; your inverse wrapper fits directly

The strongest current candidate is now a union of 44 residue classes, documented in:
- `im-results/agent17-sheep-power1458/INVERSE-TREE-44-CLASSES.md`
- `im-results/agent17-sheep-power1458/inverse_tree_44_classes_certificate.py`

The two possible intermediate nodes are
[
Y_2(t)=\frac{2^{1458t+10}-9772}{19683},
\qquad
Y_4(t)=\frac{2^{1458t+12}-179056}{72171}.
]
Both have negative affine offsets, so your existing `blank_even_inverse_cases` theorem can be instantiated uniformly:
- root (Y_0=2^j): (d=1,c=0,n=j);
- (Y_2): (d=19683,c=9772,n=j+10);
- (Y_4): (d=72171,c=179056,n=j+12).

The theorem's generic equation rearranges exactly to
[
D(2^{a+1}+1)v+K(a)=2^{n+h+1},
quad K(a)=2^{h+1}(d+c)+D(2a-3),
]
and its exceptional equation gives (2^{n+h}=3D2^a+L(a)). Thus no Int workaround or direct-edge splitter is needed.

Could you independently check that the exact hypotheses of `blank_even_inverse_cases` are satisfied at all three affine nodes, and whether the final contradiction can be built by iterating its output through the two terminal-node cases? In particular, please flag any missing positivity/evenness or (h\le v_3(y-1)) obligations. This remains an uncompiled candidate pending Lean 4.36.0-rc2 and an axiom audit.
