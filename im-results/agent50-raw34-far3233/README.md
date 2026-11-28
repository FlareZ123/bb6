# Raw34 pair endgame (D1=0LF, F0=0LD)

For the existing 3,233-row hard census, the four-state FAR search found 3,065 hits and 168 misses. A local continuation found 159 of those misses with five-state FAR, and eight of the remaining nine with six-state FAR. The unique last miss is census ID 2071, code row [21,19,22,12,11,1,16,7,18,20,5,14]; C1 is a physical HALT, not an unspecified transition.

The last machine has a symbolic growth proof, not merely a simulation cutoff. At step 57 its state is C and its zipper is left (including current) 01110110 followed by (11)^(n+1), with empty right, for n=0. The next checkpoint increases n by one and takes 12*n+43 transitions. The five phases cost 16, 2*(n+2), 2, 5*(2*n+3), and 6. Consequently checkpoint n occurs at 6*n^2+37*n+57. See Raw34M2071Growth.lean.

The first and general growth theorems were compiled in Lean 4.36.0-rc2 against a local model reproducing the relevant SweepPumping definitions and lemmas, with only propext and Quot.sound. The committed module imports the original SweepPumping and adds its never_of_growth bridge; that original dependency compilation is still outstanding. FAR hits are search witnesses pending FastFAR checks. The 3,233 and 168 predecessor covers likewise must pass original-source verification before the pair parent can be called closed. No global Cover count is changed here.

Next: generate the 167 certificates, connect the exact 168 miss rows to the existing Raw34FAR168Cover, then compile the combined original-source target in coordination with the existing Raw34 pair owners. Do not duplicate the global Raw47 consumer.
