# Residual 3863: translated left half-line cycle

Exact partial table [7,10,11,21,14,17,24,16,20,11,3,0], unknown D0.

The buffered sweep search identified an entry at 30,522 primitive steps (state A, head -262), and recurrence at 92,257 (state A, head -611). The maximum consulted head coordinate during the intervening 61,735 steps is -169; the complete tape on x <= -169 agrees after translation by -349. Both left zipper lists at the endpoints are [false,true], and the first 93 right bits coincide. This is a mathematical nonhalting certificate for every compatible completion, by the existing sideCycle_never theorem.

An independent primitive set-of-ones replay confirmed the exact witness. The original Lean fastSideCycleCheck also evaluated to true at boundary -165 (a slightly larger retained half-line). A monolithic kernel reduction of the old list-of-ones checker was too expensive. E0LFZipSideCycle.lean proves a reusable linear zipper window replay and half-line comparison theorem, compiled locally against artifact 15126193553 with only propext, Classical.choice, Quot.sound. emit_cycle3863.py generates the concrete 512-step chunked rfl proofs and balanced join tree. Concrete full kernel audit is in progress; the general soundness theorem is already locally accepted. The final theorem is BB6.Agent3E0LF3863.never3863. 
