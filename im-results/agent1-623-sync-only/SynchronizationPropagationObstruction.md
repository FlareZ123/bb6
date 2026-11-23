# Minimal obstruction to a generic synchronization-propagation lemma for machine #623

**Status:** exact finite counterexamples to an overly strong induction principle. They do not occur as asserted authentic root transitions; they show which extra joint phase constraints an all-time proof must retain.

The exact four-residue theorem makes it tempting to hope that an input word which synchronizes the full L/R carry rectangles always produces an output word which is again synchronizing. That is false even when the starting transducer state is taken from the boundary-state combinations present in the current authentic S-window phase catalogue.

All words below have length 3, hence M=27. Pair codes are 3x+y.

## Left-branch counterexample

Take the input word `[0,1,0]`, i.e.

\[(00),(01),(00).\]

It has word values X=0, Y=3. Its four synchronization residues are

\[[X-3Y]_{27}=18,\quad [3Y]_{27}=9,\quad [4X+3Y]_{27}=9,\quad [3(X+Y)]_{27}=9,\]

so it synchronizes both full rectangles.

Start the L transducer from

\[(x_{-1},y_{-1})=(2,0),\qquad (a_0,b_0)=(0,0).\]

This boundary combination occurs in the current `SWindowEdgeRecords.json` phase catalogue. The output word is `[0,0,7]`, i.e.

\[(00),(00),(21).\]

Thus X'=18, Y'=9. Its residues include

\[[3Y']_{27}=0,\qquad [3(X'+Y')]_{27}=0,\]

so the output fails synchronization.

## Right-branch counterexample

Use the same synchronized input word `[0,1,0]`, but start the R transducer from

\[(x_{-1},y_{-1})=(0,0),\qquad (a_0,b_0)=(-2,1).\]

This combination also occurs in the current phase catalogue. The output word is `[4,6,4]`, i.e.

\[(11),(20),(11).\]

So X'=16, Y'=10. The first three synchronization residues are safe, but

\[[3(X'+Y')]_{27}=24>20=M-7,\]

and the output again fails.

## Consequence

Neither of the following is a valid induction invariant by itself:

1. the source word synchronizes both full carry rectangles;
2. the source word synchronizes and the entering boundary state belongs to the union of boundary states seen in the current authentic phase catalogue.

The missing information is a **joint compatibility relation** between the boundary state, source sector/drain statistics, and the actual digit word. This explains why the old phase product remained large and why simply replacing it by the 70-state synchronization DFA cannot close the root proof.

The useful reduction remains the exact four-residue criterion and the terminal-to-synchronization-failure bridge. A successful induction must propagate a source-derived relation on the two residue coordinates together with enough low-boundary carry data to exclude the witnesses above.
