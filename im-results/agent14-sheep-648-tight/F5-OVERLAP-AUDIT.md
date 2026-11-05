# Complete overlap audit against the existing fifth-depth F sieve

Agent 14, 2026-11-05 19:40 UTC. Scientific comparison, exact computational replication.

I reconstructed the complete `im-results/agent17-sheep-third-generation/symbolic_sieve.py` modular inverse grammar with the same depth-five extension used by Agent16, then recomputed **all 5,400 candidate exponent residues**, not merely the 25 of interest. Exact results:

- 3,596 excluded classes modulo 5,400.
- SHA256 of the comma-separated sorted 3,596 residues: `dc77776f9a51938d6c6e1fdb57be681477dae9b93d54fa351d4d4f9ae4b6555b`, exactly matching the previously published Agent16 depth-five certificate.
- The tightened E progression `j=648+17496k` visits precisely the 25 residue classes modulo 5,400 that are divisible by 216. This follows from `gcd(17496,5400)=216` and `648=3*216`.
- **None of those 25 classes is in the published excluded F depth-five list.** Exact intersection size zero, independently verified after reproducing the entire original class-list digest.
- The earlier `j=648+122472k` E progression also visits all 25 such classes modulo 5,400, so the tightened E theorem's six new phases add entirely new relative coverage beyond the existing F sieve. The previous [README.md](README.md) also verifies disjointness from the fifteen other compared E families.

Hence the extra density beyond the combined published F depth-five and the old 648 E family is exactly `6/122472=1/20412`, *provided* the other 15 compared E families remain as recorded and the strengthened paper/exact-integer E certificate is accepted. This is arithmetic exponent coverage only, with no halting probability interpretation.

The standalone recreated verifier `sheep648_f5_overlap.py` is available as a user-visible artifact, SHA256 `b4a26911cb4b948713b8c39a81a4c5e06b4b9cbef806209ad6f4d128ce66e5a2`. It uses SymPy for exact modular orders and asserts both the complete 3,596 count and published digest before checking the 25-class intersection. The current complete strengthened E claim is paper/exact-integer, with the new Z-leaf and phase exception primitives locally Lean-compiled and original-machine source integration outstanding.