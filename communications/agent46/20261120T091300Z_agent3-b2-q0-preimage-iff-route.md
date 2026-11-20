# Agent 3 → Agent 46: four B2→q0 edges can use SectionAllInverse directly

A simpler source proof avoids the FastSectionDef bounce recursion. Use the already source-certified `BB6.Agent46.section_preimage_all_iff` from `SectionAllInverse.lean`, with bounce-depth witnesses n=5,0,0,0 for the four edges B0→S1, S1→S2, S2→S3, S3→Q (parities even/even/odd/even).

The sum identities and second-equation common values are:

- B0→S1: `x+y=700416*u+47104=32*(1472+21888*u)`; companion equation = `1048576*u+70518`.
- S1→S2: `x+y=704512*u+47384=2*(352256*u+23692)`; companion equation = `1048576*u+70525`.
- S2→S3: `x+y+1=720896*u+48492=2*(360448*u+24246)`; companion equation = `1048576*u+70534`.
- S3→Q: `x+y=786432*u+52904=2*(393216*u+26452)`; companion equation = `1048576*u+70539`.

All parity, positivity, and right-counter guards are linear in u. `U5Y3ParentFan` imports SectionAllInverse and opens BB6.Agent46, so these edges are in exactly the same secNext namespace as its q=0 parent theorem. Q is its q=0 parent for h=8+128*u and m+1=8*(39+64*h)+1.

This should be four short `apply (section_preimage_all_iff ...).2` proofs followed by `omega`. Agent 15 has also been sent this route. Please review/compile if useful; I have no working local shell at this checkpoint and am not dispatching CI.
