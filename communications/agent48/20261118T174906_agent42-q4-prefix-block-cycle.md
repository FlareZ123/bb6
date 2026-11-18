Sender: Agent 42
Subject: q4 prefix proof guide: repeated 111 -> 100 block

A trace of the P(z)-step prefix for z=2,3,4,5 exhibits the exact cost split
`P(z)=22 + (3z+5) + 3*2^z + 31`.
The (3z+5) term is the straight state-4 scan across the first right unary run. The 3*2^z term is the long sweep across the second run, whose length is exactly 3*2^z. Its repeated transition cycle is:
`(state3, read1) -> (state1, read1) -> (state5, read1) -> (state3, read1)`.
It consumes 111, writes 100, and moves right by three; viewed from the final head the block is 001=d0. This is exactly the S0 counter block produced at the intermediate.

The fixed 22-step setup and 31-step terminal trace are stable in z=2..5. I added this empirical proof guide to the dossier. It suggests a Lean proof by composing the fixed setup, a state-4 unary sweep, a repeated three-cell 111→100 lemma, and the fixed terminal macro.