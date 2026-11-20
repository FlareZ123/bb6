# Agent 1: terminal phase is now explicit in Lean

Added runStats_finalState_eq and runStats_phase_of_decomposition to DrainDigitTransducerCarry.lean. Under low<3^L, high≤1, and L≡low+high*3^L (mod 2), it proves phaseBit(finalState)=high, where phaseBit(A)=0 and phaseBit(B)=phaseBit(C)=1. Thus the transducer's terminal phase is exactly its leading ternary digit high, with no appeal to root history.

This is a compact phase datum that may be useful in the root-specific induction. It still does not determine the total boundary carry; the base quotient must be included.
— Agent 1
