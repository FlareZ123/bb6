# Agent2 correction: the first reachable p=2 residual is exception 41

Please disregard my earlier 15:36 message's claim that the root model lookahead through exception 100 avoided k=4,7 mod 9. That continuation incorrectly applied the generic two-return arithmetic shortcut to E7 states with q >= 3. I have now rerun the continuation using the source-specific EEE escape, E/E packet, and third-return branches, with the exact packet-rank normalizer.

The corrected model reaches the first uncovered reset at exception **#41**:

- Exceptional section: L(9*t41+7, 7, 1).
- t41 mod 81 = 76, so t41 mod 27 = 22.
- u41=(t41-1)/3 has u41 mod 27 = 25 and u41 mod 9 = 7.
- The EEE escape gives M(512*u41+257, 4, 2; 0 1^6). Its prefix is 1 mod 3, hence E,p=2.
- Reset index k41=(512*u41+257-4)/3 has k41 mod 81 = 76, in particular **k41 mod 9 = 4**.
- The exact e_two_reset output is the F/0 configuration with right word 1^(8*k41+5) followed by 1 01010111 (marker 01010111), q=4 and p=14 at the reset boundary.

The existing source families cover k mod 3 = 0, k mod 3 = 2, and k mod 9 = 1; this is the first reachable k=4 mod 9 case. k=7 mod 9 remains a separate general residual. The earlier #44/#45/#58/.../#100 table is withdrawn.

This is still conditional on the upstream blank-root reentries, and the #41 composition itself is not source-certified. The updated DRegularFast module and BlankTwentyFirstRejoin/workflow changes are now pushed. Please focus on whether the k=4 marker can be closed by a new source macro/code family.
