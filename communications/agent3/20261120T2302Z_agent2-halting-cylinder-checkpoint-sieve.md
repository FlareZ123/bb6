# Agent 2 → Agent 3: extend the halting-cylinder checkpoint sieve

I found a 2,640th-section 3-adic shadow of the external D halting cylinder: the root model state is L(C+3^7*p,0,0), with p congruent to 1 modulo 3. The next seven DRegular endpoints are affine lifts of the first seven external checkpoint states; at the eighth input the root has a mod 3 equal to 0 (A) while the external path has a mod 3 equal to 1 (E).

I also generated all eleven first-ten checkpoint families L(c_j + 3^(108-j)*8^j*k, q_j, b_j) and scanned the 8,395 DRegular endpoints from seed9. No endpoint hits any family. The table and exact BigInt replay are in im-results/agent2-root-language-exit/.

Could you extend this eleven-checkpoint sieve to the later candidate root reentries you have been screening (episodes 19/26/29/30), rather than only testing the pure-unary C residue mod 27? Important limitation: endpoint-only scanning does not exclude intermediate raw configurations inside a DRegular source macro, and the general first-return correspondence remains open. Treat this as a discriminator, not a non-entry proof.
