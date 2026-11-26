# Raw139 E0=0LF residues 3862/3863: exact buffered sweep interface

These two original one-hole machines differ only in B1 (19 versus 21). They have D0 unknown. This is a source-checked reduction, not a decision of either residual.

[E0LFSweep.lean](E0LFSweep.lean) supplies 16 positive-cost prefix rules per variant, covering the blank-start orbit after 9 primitive steps. Each rule is an exact execution on arbitrary finite tape tails, not a bounded simulation. A and C read exclusively the right stack, E and Z exclusively the left stack. Known boundary bits are omitted from the stack representation. The sole unsafe physical excursion is E with nearest-first left prefix 01100, or equivalently Z with prefix 1100. Both reach D0 in four known primitive steps. At all other padded configurations one rule applies. The initial buffered configuration is A at h=-1 with L empty, R=0011 (nearest first). No completion of D0 is used by any rule.

The proof interface is `Stable alt I`: initial membership, padding invariance, exclusion of Bad, and closure under the explicit rules. `stable_never` proves `NeverHalts m` for every compatible completion of the original table from these four premises. The latter invariant remains missing. An implementation must handle arbitrary stack lengths, not just observed configurations.

The one-way scan structure enables rational transduction of complete right/left sweeps. The left parser of the E scan has seven states (including success/failure). With symbols ordered 0,1 its transition rows are (1,0), (5,2), (0,3), (4,1), (6,0), (5,5), (6,6). The initial state is 0; 5 and 6 are absorbing successful return and D0 query. The Z scan starts at state 1. At an infinite zero suffix the safe-state vector is (true,true,true,false,false,true,false). This classifier is a search observation; the Lean module formalizes the exact prefix rules and universal invariant bridge, rather than this parser's automata implementation.

## Local checking

Lean 4.36.0-rc2; original dependencies from successful source audit artifact 15126193553, SHA256 d2a84a66d1a3f9e993538e000345fd3692847698328cf364bf9d591d96fccb69. Compile with LEAN_PATH pointing at its build directory. `bad_hit`, `rule_exact`, `seed_run`, `stable_never` report only propext and Quot.sound; `cover_padded` only propext.

## Search status

Plain finite prefix/context products, one-sided FAR saturation with the exact left scan classifier, and indiscriminate DFA widening admitted spurious bad configurations. Those are failures of particular abstractions, not evidence of halting. Focus further search on selective backward preimage refinement or an inductive regular language at sweep boundaries. No row is discharged by this intermediate result.
