# Raw40 A1=0LA C1=1LA, leaf 156: exact unbounded crossing-splice recurrence

Literal partial machine:

`1RB0LA_1RC1RE_0RD1LA_1LD1LA_---0RF_0RB0RC`

The hole is E0. This proves nonhalting of every completion by an elementary crossing-sequence splicing argument, with finite computational premises. It is a mathematical proof with an executable finite-premise checker; it is not yet a Lean theorem or an accepted parent Cover.

## Result

Let X(n,h) be state A, head h scanning zero, all cells at or left of h blank, with right word

`00000 1^(48+21n) (0111111)^(6+3n) 011111`

and all further cells blank. The blank run reaches X(0,-42) after 2340 moves. For every natural n and integer h the assigned transitions take X(n,h) to X(n+1,h-18) in exactly 2172+702n moves. Therefore the blank execution has arbitrarily long defined prefixes without querying E0. The proof covers every completion regardless of its E0 instruction.

## Splicing lemma (finite computation, arbitrary repetitions)

Consider any finite computation on a one-dimensional nearest-neighbor deterministic TM. Label the edge between cells x and x+1 by the chronological list of crossings (direction, state after the crossing). Label each cell by its initial bit, ordered visits with arriving state and side, local transition (or final stop marker), and final bit. Record the actual computation's starting and ending head and state. Suppose a<b, neither endpoint head belongs to (a,b], and the edge lists at a and b are identical. Inserting any number of extra copies of the cell transcripts in (a,b], shifting the suffix, yields a valid finite computation on the correspondingly expanded initial tape, ending with the correspondingly expanded final tape. The number of moves increases by the total number of departures from the copied cells per copy.

Proof. Every local transcript is transition-valid, and the spliced interfaces agree because their edge lists agree. Start at the unique initial visit. At each departure, the next crossing on that edge has the same direction and arriving state in both endpoint transcripts, since their already consumed crossings coincide. The next visit at the destination must be from that edge: if it has been visited before, its previous departure must have been toward the current head (otherwise the head would have had to revisit it); if never visited, the side follows from the starting head position. The destination thus expects this arrival, and its next recorded transition is the machine's actual transition. No extra visit to a fully consumed cell is possible, because it would require an unrecorded crossing of its incident edge. Each transition consumes one departure, so the process reaches the final marker in finitely many moves. At that point no unconsumed transcript exists elsewhere: the final cell's incident edges are exhausted, and an adjacent cell with an unconsumed visit would have to next be entered from the side on which the current head lies, contradicting exhaustion of the intervening edge. Propagate this argument outwards through the finite support of the transcripts. All moves have therefore been consumed, and every cell has its recorded final bit. The same proof works for simultaneous repetitions of any disjoint matching intervals. Translation of the entire construction preserves every local transition. Blank unvisited cells outside the finite transcript remain blank.

## Exact finite premises

In the 2172-move base transition from X(0,0) to X(1,-18), the matching edge pairs are (5,26) and (63,84). Both pump intervals are strictly to the right of both endpoint heads. Their respective departure counts are 294 and 408. The first interval consists of 21 ones in both input and output. The second consists of three periods of length seven in both input and output (the phases need not be identical between input and output). Duplicating both intervals n times thus adds 21 ones and 3 tail blocks to both endpoint words, leaving heads fixed. The expanded start and finish are X(n,0) and X(n+1,-18). The move count is 2172+(294+408)n. The executable checker verifies the blank entry, the literal base transition, both identical edge lists, the input/output word identities and the counts, with no unassigned query.

This avoids extrapolating a simulated recurrence: the finite trace and edge equalities supply the induction for every n. No conjecture about future sweep patterns is required.

## Consumption

This was the remaining leaf in the saved C1=1LA bank after the separate translated-cycle certificate for leaf 161. Agent19 can use this exact recurrence to implement a Lean completion theorem and close the full C1=1LA child through its existing checker. Until the source theorem is accepted, no parent or global decrement is asserted.
