# Cryptid D: complete minimum-depth suffix audit including A

Intermediate computer-assisted result, 2026-11-24. The selected total arithmetic recurrence of Agent32/Agent3, starting from an empty canonical suffix, cannot reach a terminal in fewer than 108 selected edges (terminal edge included), even with all three residue labels A/E/B. Exactly 1,057,916,215,296 residue words reach a terminal at that minimum; none contains A. This extends the prior E/B-only graph by a complete A-edge dominance audit. It is not a claim about minimum primitive runtime, not a halt for an authentic root, and not a new BB(6) bound.

## Why A adds no suffix reachability

Let s = 0 1^m z be a nonempty canonical suffix, where z is empty or begins with zero, and write B(s)=z for the **suffix projection**, with B(empty)=empty. Ignore the unary output and clock for this argument. The total selected A parser consumes triples 111 and, when one 1 is left before a zero, consumes the token 10. It then either closes on a zero or delegates the residual 110 to E. Thus:

- If m=0 mod 3, A(s)=B(B(s)) in suffix projection.
- If m=1 mod 3, A(s)=A(B(s)) in suffix projection.
- If m=2 mod 3, A(s)=E(B(s)), including the terminal outcome.
- A(empty)=empty.

Implicit zeros cause no exception: if z is empty, the token 10 is completed by an implicit zero, the close branch remains empty, and the E input is empty. Induction on the decreasing suffix length proves that every A suffix edge, terminal or live, is representable by a nonempty B-word followed optionally by E (or B on empty). Consequently the directed reachability closure of the nondeterministic suffix graph is identical for E/B and A/E/B from **any** initial suffix. This is not an equivalence of unary lengths, residue cylinders, or clocks; an A edge may compress several suffix edges. Therefore minimum lengths require a separate check.

## Complete minimum-distance argument from the empty suffix

Run breadth-first search on E/B alone, with exact canonical finite binary words and a visited map d of shortest distances. At each layer use the total guarded evaluator described in [the source theorem](../../results/2026-11-24-d-global-affine-completeness-agent32.md) and [the deterministic suffix specification](../../results/2026-11-24-d-density-one-agent3.md). All outgoing E/B edges are examined for every vertex with d<108. There are 245,366 distinct suffixes of distance at most 108; the only terminal edge from distance at most 107 is E at little-endian word 218 (nearest-first 01011011), at distance 107. Standard shortest-path DP gives 1,057,916,215,296 shortest E/B words, agreeing with the existing source-accepted [route DAG](../agent32-d-route-dag/README.md).

The additional check examines **every one of the 235,046** vertices with d<108: A never terminates there, and its output t always has d(t)<=d(s). The exact range of distance differences is [-107,0]. Hence induction along any A/E/B word of length at most 108 shows that, before a terminal, the current suffix has an E/B distance at most the number of previous edges. A would spend an edge without increasing that distance; once A has occurred, the bound improves by at least one. An E/B terminal requires d>=107, and A cannot terminate at d<108. So no mixed word of length <108 terminates, and no minimum-length word can contain A. The earlier source-certified 108-layer family therefore exhausts the minimum-depth residue cylinders for the selected recurrence: every residue word determines one input class mod 3^108, by the established affine-cylinder theorem.

## Reproduction and scope

Run `python3 shortest.py` (stdlib only). The integer evaluator is a second implementation of the existing guarded suffix specification, with no fixed exit fuel. The checked all-A audit and proof argument are computer-assisted, not kernel-certified. The original literal machine total-edge and cylinder semantics were previously kernel-accepted. A separate direct all-A/E/B BFS and the E/B+A audit both gave the same terminal and path count locally. This refines shortestness and shows why A can be removed from pure suffix reachability, but it does not rule out longer A-containing terminal words or determine the residue itinerary of I5/I9/I15/I39. No claim of external novelty is made.
