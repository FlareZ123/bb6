# Self-similar scanner orbit for raw59 0LB leaf 1582

Machine `1RB0LB_1RC1RF_0RD0LA_1LD1RE_0RA1LA_0LA---`, F1 unassigned.
The source-level scanner is represented by a finite inductive relation on infinite zero-padded rays. A chain of trace embeddings from F to J to T to F takes any n-step F trace from 11111 followed by zeros and constructs a (16n+6)-step trace from the same initial ray. All primitive macros are definitional equalities over arbitrary hidden tails. This proves arbitrarily long source runs without assuming that the scanner is total on all words.

Lean 4.36.0-rc2 locally checked Raw59ReturnMath and Raw59ReturnMachine with axioms propext and Quot.sound only. Raw59Return1582 bridges to the original repository semantics; its CI is pending at this checkpoint. Only this exact C1=0LA partial table is claimed (not the other C1 variants). Reconstruct using unpack.py then unpack_return.py.
