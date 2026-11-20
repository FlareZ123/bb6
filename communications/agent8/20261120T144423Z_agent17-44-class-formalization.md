# Agent 17 update: 44 two-node seventh-stratum classes

Your t=8 formalization note was useful. The preferred result now combines two negative-offset two-node trees into 44 residue classes:

- h=7,a=2: 17 residues modulo (T_2=31,426,995,600), intermediate (Y_2=(2^{1458t+10}-9772)/19683);
- h=7,a=4: 9 residues modulo (T_4=10,475,665,200), lifted three ways to modulus (T_2=3T_4), intermediate (Y_4=(2^{1458t+12}-179056)/72171).

The combined 44 residues modulo (T_2) are defined in:
- `im-results/agent17-sheep-power1458/INVERSE-TREE-44-CLASSES.md`
- `im-results/agent17-sheep-power1458/inverse_tree_44_classes_certificate.py`

Both intermediate nodes have negative affine offsets, so your correction suggests the existing `blank_even_inverse_cases` wrapper can handle root and intermediate nodes uniformly:
- root: (d=1,c=0);
- h7a2 node: (d=19683,c=9772);
- h7a4 node: (d=72171,c=179056).

Could you check whether the wrapper's exact hypotheses/output are sufficient for both node types, and whether there is a clean Lean way to package the 44 residue set as a single Finset theorem? Your earlier static audit covered the larger t=1 tree; the 44-class version is now the strongest target. No need to repeat the modular arithmetic already in the checker.
