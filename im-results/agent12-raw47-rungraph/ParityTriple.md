# Three Raw47 hard leaves: common parity invariant

**Source-accepted:** `Raw47ParityTriple.lean` establishes `never` for all three literal tables (historical IDs 9918, 9919, 9920), and the exact parent 547 quotient audit at weighted bound 10006. CI [45971469291](https://github.com/FlareZ123/bb6/actions/runs/45971469291), job 140412733983, artifact 15185766874, SHA256 7f34356f8c4ed4e1d246cf9a3fa01f4bac235ffe236f6e641212dbbc94e97978. No global BB6 bound claimed.

The machines differ only in E0: 0RA, 0RC, 1LC. Their one undefined slot is F0. At a return to A0, the left ray is all zeros (possibly explicit padding), the right ray is a finite word of digits encoded 0=10 and 1=1110. Define Good(w) by countZeros(w) mod 2=0. This holds for the initial empty word.

The original raw-step recurrence has exactly these three cases:

- w=0^(2j)1s -> 0 1^j 0 s, cost 8j+8.
- w=0^(2j+1)1s -> 1^(j+1) 0 s, cost 8j+8+d, where d is 2,22,24 according to E0.
- w=0^(2j) -> 1^(j+1), cost 8j+13 (the all-zero odd case contradicts Good).

The even and odd prefix cases change zero-count by an even number; the all-zero case resets it to zero. Each cost is positive. The variant-specific singleton detour for E0=0RC or 1LC requires a following 1 after the first 1110 block, not arbitrary suffix. The odd branch guarantees this via the trailing encoded zero 10. This condition is explicit in the Lean detour theorem. The kernel proves all three step recurrences from framed sweeps and finite `rfl` computations, then the parity preservation and existence of arbitrarily long defined runs, transported to original machine semantics via the zipper soundness theorem. Every completion of F0 is nonhalting.

Parent547 contains 40 cap10000 open leaves: 21 FAR, 16 run-graph, and these three exact nonhalting proofs. Its full parent audit independently checks literal-table equality and the first-hole tree. See `generate_graph_parents.py` in the Agent50 Raw47 directory for integration.
