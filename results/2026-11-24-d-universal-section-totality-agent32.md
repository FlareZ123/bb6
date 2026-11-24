# Universal first-event totality for Cryptid D (Agent 32, 2026-11-24)

**Theorem (original source, local Lean 4.36.0-rc2).** For the six-state table `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`, take an arbitrary finite binary word x and initial tape with all blanks to the left, F scanning a zero, and right word 11x followed by blank continuation. At a finite strictly positive primitive time t the machine either reaches F scanning 0 with the whole left tape blank, or reaches F scanning 1 (the halt gate). There is a least such positive time, with neither event at any earlier positive time. This holds for all finite x without restrictions on its form or length. Lean declaration `BB6.OneSided.every_prepared_F_first` has axiom profile [propext, Classical.choice, Quot.sound].

## Proof

1. Establish a uniform finite right-half first exit for every finite word and every live state, independently of untouched left context. For the nested A/B recursion use the well-founded rank R(w)=length(trim(w))+2 times the number of 011 occurrences in trim(w), where trim removes trailing zeros. A 294-row weighted inductive certificate on six initial bits plus a long flag bounds the recursive return rank increments. In particular an A-to-A return cannot increase R, permitting the nested B recursion to descend. C/D/E/F are direct source transitions. All calls have exact primitive-time witnesses and frame the unvisited left tape.
2. Refine the return classification to eight initial canonical bits plus a long flag. Kernel-check 1086 unweighted summary rows (536 A and 550 B), and lift this classification through the same rank induction. The finite walk then consumes the prepared A/B alternating left stack through three pairs, or E through four, to stable C/0 or D/0; E at exactly three pairs has a separate checked terminal case. D has a direct sweep; C reaches a finite return or reduces to a blank-left A front.
3. For a blank-left A scanning 0 with right word 11(01)^m z, m>=3, prove eventual event by induction on the length of z, not on the size of the alternating prefix. An initial 01 is absorbed into the alternating prefix, and initial 11 z leads to the larger prefix (01)^(m+3) and strictly shorter tail 0z. Other initial pairs and the short tails terminate using the B-pair stabilization lemma. Hence this phase cannot escape forever even though its alternating prefix can grow.
4. Compose the original source F-prefix equations for all three residues (including implicit blank delimiters) with the preceding sector theorems, and choose the least positive event time.

The finite certificates are overapproximations of actual returns, verified by kernel reduction; they are not finite evidence for unbounded assertions. All inductions are in Lean, with no sorry, admit or native_decide. This proof independently eliminates infinite intra-section escape for all three residues, including the former A extension problem, without using the prior E-marker safety theorem.

## Significance and limits

This removes a substantive missing totality obligation in reducing D's primitive dynamics to repeated F sections. It does not establish that the section-level trajectory of any one of the four authentic roots reaches the halt gate, nor that it avoids it forever. No BB(6) upper/lower bound improvement or fixed-root decision is claimed. External novelty beyond the repository has not been assessed.

## Reproduction

[Proof dossier, exact archives, certificate counts and build instructions](../im-results/agent32-d-onesided-total/README.md). Run `bash im-results/agent32-d-onesided-total/reproduce-all.sh` with Lean 4.36.0-rc2 available. The exact local proof archive is SHA256 06286109fd7afbfa611f23a551bc0fc8d774bdfde18481aa666310e77cf9caa8; its three remote parts were checked against the corresponding local Git blob hashes. Independent CI reproduction has not been performed.
